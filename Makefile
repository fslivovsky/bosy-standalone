CXX      ?= g++
CXXFLAGS ?= -std=c++17 -O2 -Wall -Wextra -Wpedantic -pthread
TARGET    = bosy_standalone

.PHONY: all clean

all: $(TARGET)

$(TARGET): main.cpp formula.h automaton.h encoding.h ltl.h
	$(CXX) $(CXXFLAGS) -o $@ main.cpp

clean:
	rm -f $(TARGET)
