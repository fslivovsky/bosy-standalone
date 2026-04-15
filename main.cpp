// main.cpp -- CLI entry point, JSON parser, solver invocation, bound search
//
// This is the driver for the standalone bounded-synthesis tool.  It:
//   1. Parses a BoSy JSON specification (inputs, outputs, LTL guarantees).
//   2. Negates the LTL formula and converts it to a co-Buechi automaton
//      via an external call to ltl2tgba (from the Spot library).
//   3. Encodes the bounded-synthesis problem as QBF or DQBF using one
//      of three backends (input-symbolic, state-symbolic, symbolic).
//   4. Writes the encoding to a temporary file (QDIMACS or DQDIMACS).
//   5. Calls a user-specified external solver and interprets the result.
//   6. Performs an exponential bound search (1, 2, 4, 8, ...).
//
// By default, the tool searches for a system implementation (realizable)
// and an environment counter-strategy (unrealizable) in parallel, as
// described in the BoSy paper.  The first thread to find SAT wins.
// The dual search can be disabled with --no-dual.
//
// TLSF input is not handled directly; use syfco to convert first:
//   syfco --format bosy spec.tlsf > spec.json

#include "encoding.h"

#include <iostream>
#include <fstream>
#include <sstream>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <algorithm>
#include <atomic>
#include <thread>
#include <unistd.h>
#include <sys/wait.h>

// ===================================================================
// Minimal JSON parser
//
// Only handles the BoSy specification format: a flat object with
// string values and arrays of strings.  Tolerates trailing commas.
// ===================================================================

namespace json {

inline void skipWs(const std::string& s, size_t& i) {
    while (i < s.size() && (s[i]==' '||s[i]=='\t'||s[i]=='\n'||s[i]=='\r')) ++i;
}

inline std::string parseString(const std::string& s, size_t& i) {
    if (i >= s.size() || s[i] != '"')
        throw std::runtime_error("expected '\"' in JSON");
    ++i;
    std::string r;
    while (i < s.size() && s[i] != '"') {
        if (s[i] == '\\') { ++i; if (i < s.size()) r += s[i]; }
        else r += s[i];
        ++i;
    }
    if (i < s.size()) ++i; // closing quote
    return r;
}

inline std::vector<std::string> parseStringArray(const std::string& s, size_t& i) {
    if (s[i] != '[') throw std::runtime_error("expected '[' in JSON");
    ++i;
    std::vector<std::string> r;
    skipWs(s, i);
    while (i < s.size() && s[i] != ']') {
        if (s[i] == ',') { ++i; skipWs(s, i); continue; }
        r.push_back(parseString(s, i));
        skipWs(s, i);
    }
    if (i < s.size()) ++i; // ']'
    return r;
}

} // namespace json

// Parse a BoSy JSON specification file into a Specification struct.
inline Specification parseSpec(const std::string& filename) {
    std::ifstream f(filename);
    if (!f) throw std::runtime_error("cannot open " + filename);
    std::string content((std::istreambuf_iterator<char>(f)),
                         std::istreambuf_iterator<char>());

    Specification spec;
    size_t i = 0;
    json::skipWs(content, i);
    if (content[i] != '{') throw std::runtime_error("expected '{' at start of spec");
    ++i;

    while (i < content.size() && content[i] != '}') {
        json::skipWs(content, i);
        if (i >= content.size() || content[i] == '}') break;
        if (content[i] == ',') { ++i; continue; }

        std::string key = json::parseString(content, i);
        json::skipWs(content, i);
        if (content[i] != ':') throw std::runtime_error("expected ':' after key");
        ++i; json::skipWs(content, i);

        if (key == "semantics") {
            std::string val = json::parseString(content, i);
            spec.semantics = (val == "moore") ? Specification::Moore
                                              : Specification::Mealy;
        } else if (key == "inputs") {
            spec.inputs = json::parseStringArray(content, i);
        } else if (key == "outputs") {
            spec.outputs = json::parseStringArray(content, i);
        } else if (key == "assumptions") {
            spec.assumptions = json::parseStringArray(content, i);
        } else if (key == "guarantees") {
            spec.guarantees = json::parseStringArray(content, i);
        } else {
            // skip unknown value (string or array)
            json::skipWs(content, i);
            if (i < content.size() && content[i] == '"')
                json::parseString(content, i);
            else if (i < content.size() && content[i] == '[')
                json::parseStringArray(content, i);
        }
        json::skipWs(content, i);
    }
    return spec;
}

// ===================================================================
// LTL formula construction
// ===================================================================

// Helper: join LTL strings with &.
static std::string joinLTL(const std::vector<std::string>& v) {
    std::string r;
    for (size_t i = 0; i < v.size(); ++i) {
        if (i) r += " && ";
        r += "(" + v[i] + ")";
    }
    return r;
}

// Build the (non-negated) LTL formula:  (A1 & ... & An) -> (G1 & ... & Gm)
inline std::string buildLTL(const Specification& spec) {
    std::string g = spec.guarantees.empty() ? "1" : joinLTL(spec.guarantees);
    if (spec.assumptions.empty()) return g;
    return "(" + joinLTL(spec.assumptions) + ") -> (" + g + ")";
}

// Build the negated LTL formula for ltl2tgba:
//   !(A -> G) = A & !G
inline std::string buildNegatedLTL(const Specification& spec) {
    if (spec.assumptions.empty()) {
        if (spec.guarantees.empty()) return "0";
        return "!(" + joinLTL(spec.guarantees) + ")";
    }
    return "(" + joinLTL(spec.assumptions) + ") && !("
         + joinLTL(spec.guarantees) + ")";
}

// ===================================================================
// Specification dualization
//
// Produces the "environment player" spec by:
//   - swapping inputs and outputs
//   - swapping Mealy <-> Moore semantics
//   - setting the single guarantee to !(original LTL)
//
// When buildNegatedLTL is called on the dualized spec, the double
// negation yields the original formula, so the environment automaton
// is built for (A -> G) while the system automaton is built for
// !(A -> G).  This is correct: the environment wins if it can force
// the spec to hold regardless of the system's moves (unrealizable).
// ===================================================================

inline Specification dualize(const Specification& spec) {
    Specification dual;
    dual.semantics = (spec.semantics == Specification::Mealy)
                     ? Specification::Moore : Specification::Mealy;
    dual.inputs  = spec.outputs;
    dual.outputs = spec.inputs;
    // no assumptions; single guarantee = negation of original formula
    dual.guarantees = { "!(" + buildLTL(spec) + ")" };
    return dual;
}

// ===================================================================
// External solver invocation
//
// Runs:  <solverCmd> <filePath>
// Interprets exit code 10 as SAT, 20 as UNSAT (QBF convention).
// Falls back to scanning stdout for "sat"/"unsat" keywords.
// ===================================================================

enum SolverResult { SAT, UNSAT, UNKNOWN };

inline SolverResult runSolver(const std::string& solverCmd,
                              const std::string& filePath,
                              bool verbose)
{
    std::string cmd = solverCmd + " " + filePath + " 2>&1";
    if (verbose) std::cerr << "  solver: " << cmd << "\n";

    FILE* pipe = popen(cmd.c_str(), "r");
    if (!pipe) return UNKNOWN;
    std::string output;
    char buf[4096];
    while (fgets(buf, sizeof(buf), pipe)) output += buf;
    int st = pclose(pipe);
    int exitCode = WEXITSTATUS(st);

    if (exitCode == 10) return SAT;
    if (exitCode == 20) return UNSAT;

    // fallback: check stdout keywords (case-insensitive)
    std::string lo = output;
    std::transform(lo.begin(), lo.end(), lo.begin(), ::tolower);
    if (lo.find("unsat") != std::string::npos) return UNSAT;
    if (lo.find("sat")   != std::string::npos) return SAT;
    if (verbose) std::cerr << "  solver output:\n" << output << "\n";
    return UNKNOWN;
}

// ===================================================================
// Write string to a temporary file, return its path.
// ===================================================================

inline std::string writeTempFile(const std::string& content,
                                 const std::string& suffix,
                                 const std::string& tmpDir = "/tmp")
{
    std::string tmpl = tmpDir + "/bosy_" + suffix + "_XXXXXX";
    std::vector<char> path(tmpl.begin(), tmpl.end());
    path.push_back('\0');
    int fd = mkstemp(path.data());
    if (fd < 0) throw std::runtime_error("mkstemp failed for template '"
                                        + tmpl + "': " + strerror(errno));
    size_t total = 0;
    while (total < content.size()) {
        ssize_t n = write(fd, content.data() + total, content.size() - total);
        if (n <= 0) { close(fd); throw std::runtime_error(
            "write failed for '" + std::string(path.data()) + "': " + strerror(errno)); }
        total += n;
    }
    close(fd);
    return std::string(path.data());
}

// ===================================================================
// Usage
// ===================================================================

static void usage(const char* prog) {
    std::cerr
        << "Usage: " << prog << " [options] <spec.json>\n"
        << "\n"
        << "Options:\n"
        << "  --encoding <input-symbolic|state-symbolic|symbolic>  (default: input-symbolic)\n"
        << "  --solver <command>        External QBF/DQBF solver command\n"
        << "  --ltl2tgba <path>         Path to ltl2tgba (default: ltl2tgba)\n"
        << "  --ltl3ba <path>           Use ltl3ba instead of ltl2tgba\n"
        << "  --tmp-dir <dir>           Directory for temporary files (default: /tmp)\n"
        << "  --bound <n>               Use a fixed bound (skip search)\n"
        << "  --max-bound <n>           Maximum bound for search (default: 32)\n"
        << "  --no-dual                 Disable parallel environment search\n"
        << "  --dump                    Dump the encoding to stdout and exit\n"
        << "  -v, --verbose             Verbose output\n"
        << "  -h, --help                Show this help\n"
        << "\n"
        << "For TLSF input, convert first:  syfco --format bosy spec.tlsf > spec.json\n";
}

// ===================================================================
// Main
// ===================================================================

int main(int argc, char* argv[]) {
    std::string specFile;
    std::string encoding   = "input-symbolic";
    std::string solver;
    std::string ltl2tgba   = "ltl2tgba";
    std::string ltl3ba;
    std::string tmpDir     = "/tmp";
    int fixedBound         = -1;
    int maxBound           = 32;
    bool verbose           = false;
    bool dumpOnly          = false;
    bool dualSearch        = true;

    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "-h" || a == "--help") { usage(argv[0]); return 0; }
        else if (a == "-v" || a == "--verbose") verbose = true;
        else if (a == "--dump") dumpOnly = true;
        else if (a == "--no-dual") dualSearch = false;
        else if (a == "--encoding" && i+1<argc) encoding = argv[++i];
        else if (a == "--solver"   && i+1<argc) solver   = argv[++i];
        else if (a == "--ltl2tgba" && i+1<argc) ltl2tgba = argv[++i];
        else if (a == "--ltl3ba"  && i+1<argc) ltl3ba   = argv[++i];
        else if (a == "--tmp-dir" && i+1<argc) tmpDir  = argv[++i];
        else if (a == "--bound"    && i+1<argc) fixedBound = std::atoi(argv[++i]);
        else if (a == "--max-bound"&& i+1<argc) maxBound   = std::atoi(argv[++i]);
        else if (a[0] != '-') specFile = a;
        else { std::cerr << "unknown option: " << a << "\n"; return 1; }
    }

    if (specFile.empty()) { usage(argv[0]); return 1; }

    enum EncKind { ENC_QBF, ENC_STATE_SYM, ENC_SYMBOLIC };
    EncKind encKind = ENC_QBF;
    if (encoding == "state-symbolic") encKind = ENC_STATE_SYM;
    else if (encoding == "symbolic")  encKind = ENC_SYMBOLIC;

    try {
        // 1. Parse specification
        Specification spec = parseSpec(specFile);
        if (verbose) {
            std::cerr << "Specification: "
                      << (spec.semantics == Specification::Mealy ? "mealy" : "moore")
                      << ", " << spec.inputs.size() << " inputs, "
                      << spec.outputs.size() << " outputs\n";
        }

        // 2. Build automaton for system player: !(A -> G)
        std::string sysLTL = buildNegatedLTL(spec);
        if (verbose) std::cerr << "System LTL (negated): " << sysLTL << "\n";

        CoBuchiAutomaton sysAut = ltl3ba.empty()
            ? ltlToAutomaton(sysLTL, ltl2tgba)
            : ltl3baToAutomaton(sysLTL, ltl3ba);
        if (verbose) {
            std::cerr << "System automaton: " << sysAut.states.size()
                      << " states, " << sysAut.rejectingStates.size()
                      << " rejecting\n";
        }

        // 3. Build automaton for environment player (dualized spec)
        Specification envSpec;
        CoBuchiAutomaton envAut;
        if (dualSearch && !dumpOnly) {
            envSpec = dualize(spec);
            std::string envLTL = buildNegatedLTL(envSpec);
            if (verbose) std::cerr << "Environment LTL (negated): " << envLTL << "\n";

            envAut = ltl3ba.empty()
                ? ltlToAutomaton(envLTL, ltl2tgba)
                : ltl3baToAutomaton(envLTL, ltl3ba);
            if (verbose) {
                std::cerr << "Environment automaton: " << envAut.states.size()
                          << " states, " << envAut.rejectingStates.size()
                          << " rejecting\n";
            }
        }

        // 4. Dump-only mode: print the system encoding and exit
        if (dumpOnly) {
            int b = (fixedBound > 0) ? fixedBound : 1;
            switch (encKind) {
            case ENC_QBF: {
                QBFProblem p = buildInputSymbolicQBF(sysAut, spec, b);
                std::cout << toQDIMACS(p);
                break;
            }
            case ENC_STATE_SYM: {
                DQBFProblem p = buildStateSymbolicDQBF(sysAut, spec, b);
                std::cout << toDQDIMACS(p);
                break;
            }
            case ENC_SYMBOLIC: {
                DQBFProblem p = buildSymbolicDQBF(sysAut, spec, b);
                std::cout << toDQDIMACS(p);
                break;
            }
            }
            return 0;
        }

        // 5. Solver is required for the bound search
        if (solver.empty()) {
            std::cerr << "error: --solver is required (or use --dump)\n";
            return 1;
        }

        // --- helper: encode + solve for one player at one bound ---
        auto solveOnce = [&](const CoBuchiAutomaton& aut,
                             const Specification& playerSpec,
                             int b) -> SolverResult {
            std::string encoded, suffix;
            switch (encKind) {
            case ENC_QBF: {
                QBFProblem p = buildInputSymbolicQBF(aut, playerSpec, b);
                encoded = toQDIMACS(p);
                suffix = "qdimacs";
                break;
            }
            case ENC_STATE_SYM: {
                DQBFProblem p = buildStateSymbolicDQBF(aut, playerSpec, b);
                encoded = toDQDIMACS(p);
                suffix = "dqdimacs";
                break;
            }
            case ENC_SYMBOLIC: {
                DQBFProblem p = buildSymbolicDQBF(aut, playerSpec, b);
                encoded = toDQDIMACS(p);
                suffix = "dqdimacs";
                break;
            }
            }
            std::string path = writeTempFile(encoded, suffix, tmpDir);
            SolverResult res = runSolver(solver, path, verbose);
            unlink(path.c_str());
            return res;
        };

        // ===========================================================
        // 6. Parallel bound search (system + environment)
        //
        // Two threads race: one searches for a system strategy
        // (realizable), the other for an environment counter-strategy
        // (unrealizable).  The first to find SAT cancels the other.
        // ===========================================================

        // winner:  0 = none yet,  1 = system,  2 = environment
        std::atomic<int> winner{0};
        std::atomic<bool> cancelled{false};
        int sysBound = 0, envBound = 0;

        auto searchLoop = [&](const CoBuchiAutomaton& aut,
                              const Specification& playerSpec,
                              const char* label, int playerId,
                              int& resultBound) {
            for (int b = 1; b <= maxBound && !cancelled; b = (b == 1) ? 2 : b * 2) {
                if (cancelled) break;
                if (verbose)
                    std::cerr << "  [" << label << "] trying bound " << b << " ...\n";
                SolverResult r = solveOnce(aut, playerSpec, b);
                if (r == SAT) {
                    resultBound = b;
                    winner = playerId;
                    cancelled = true;
                    return;
                }
                if (r == UNKNOWN && verbose)
                    std::cerr << "  [" << label << "] UNKNOWN at bound " << b << "\n";
            }
        };

        if (fixedBound > 0) {
            // --- fixed bound: try both players at this bound ---
            if (verbose) std::cerr << "  [system] trying bound " << fixedBound << " ...\n";
            SolverResult sr = solveOnce(sysAut, spec, fixedBound);
            if (sr == SAT) {
                std::cout << "REALIZABLE (bound " << fixedBound << ")\n";
                return 0;
            }
            if (dualSearch) {
                if (verbose) std::cerr << "  [environment] trying bound " << fixedBound << " ...\n";
                SolverResult er = solveOnce(envAut, envSpec, fixedBound);
                if (er == SAT) {
                    std::cout << "UNREALIZABLE (bound " << fixedBound << ")\n";
                    return 0;
                }
            }
            std::cout << "UNKNOWN (bound " << fixedBound << ")\n";
            return 2;
        }

        if (!dualSearch) {
            // --- single-player search (system only) ---
            searchLoop(sysAut, spec, "system", 1, sysBound);
            if (winner == 1) {
                std::cout << "REALIZABLE (bound " << sysBound << ")\n";
                return 0;
            }
            std::cout << "UNREALIZABLE (searched up to bound " << maxBound << ")\n";
            return 1;
        }

        // --- dual parallel search ---
        std::thread sysThread([&]() {
            searchLoop(sysAut, spec, "system", 1, sysBound);
        });
        std::thread envThread([&]() {
            searchLoop(envAut, envSpec, "environment", 2, envBound);
        });

        sysThread.join();
        envThread.join();

        if (winner == 1) {
            std::cout << "REALIZABLE (bound " << sysBound << ")\n";
            return 0;
        } else if (winner == 2) {
            std::cout << "UNREALIZABLE (bound " << envBound << ")\n";
            return 0;
        }
        std::cout << "UNKNOWN (searched up to bound " << maxBound << ")\n";
        return 2;

    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << "\n";
        return 1;
    }
}
