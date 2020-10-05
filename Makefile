
CXX := c++ -std=c++14 -stdlib=libc++ -Iinclude -g
CXX_Z3 := -I<z3_dir> /Users/alexanderroot/Projects/z3/build/libz3.dylib

BUILD_DIR := build
SRC_DIR := src
INC_DIR := include

SRC_FILES := $(wildcard $(SRC_DIR)/*.cpp)
OBJ_FILES := $(patsubst $(SRC_DIR)/%.cpp, $(BUILD_DIR)/%.o, $(SRC_FILES))

.PRECIOUS: $(BUILD_DIR)/%.o
$(BUILD_DIR)/%.o: $(SRC_DIR)/%.cpp $(INC_DIR)/%.h
	$(CXX) $< -c -o $@

%.out: %.cpp $(OBJ_FILES) 
	$(CXX) $(CXX_Z3) $< $(OBJ_FILES) -o $@

.PHONY: clean
clean:
	rm -rf $(BUILD_DIR)/* *.out *.dSYM
