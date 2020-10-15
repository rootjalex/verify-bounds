# verify-bounds
Verification of [Halide](https://halide-lang.org "Halide Homepage") bounds inference engine


# Building with CMake / vcpkg

First, install vcpkg to some directory. For example:

```console
dev@host:~$ git clone https://github.com/microsoft/vcpkg.git
dev@host:~$ cd vcpkg
dev@host:~/vcpkg$ ./bootstrap-vcpkg.sh
```

This project depends on Z3, which depends on Python 2. Ensure you
have the `python` executable in your path pointing to Python 2.

Then clone this repo and build:

```
dev@host:~$ git clone https://github.com/rootjalex/verify-bounds
dev@host:~$ cd verify-bounds
dev@host:~/verify-bounds$ cmake -DCMAKE_TOOLCHAIN_FILE=~/vcpkg/scripts/buildsystems/vcpkg.cmake -S . -B build
-- Running vcpkg install
-- Running vcpkg install - done
-- The C compiler identification is GNU 9.3.0
-- The CXX compiler identification is GNU 9.3.0
-- Detecting C compiler ABI info
-- Detecting C compiler ABI info - done
-- Check for working C compiler: /usr/bin/cc - skipped
-- Detecting C compile features
-- Detecting C compile features - done
-- Detecting CXX compiler ABI info
-- Detecting CXX compiler ABI info - done
-- Check for working CXX compiler: /usr/bin/c++ - skipped
-- Detecting CXX compile features
-- Detecting CXX compile features - done
-- Configuring done
-- Generating done
-- Build files have been written to: /home/dev/verify-bounds/build
dev@host:~/verify-bounds$ cmake --build build
[  7%] Building CXX object CMakeFiles/core.dir/src/Bound.cpp.o
...
Scanning dependencies of target add
[ 92%] Building CXX object CMakeFiles/add.dir/add.cpp.o
[100%] Linking CXX executable add
[100%] Built target add
dev@host:~/verify-bounds$ ls build
... add   div-check   mul   sub ...
```

Then you can run any of the checks.

```
dev@host:~/verify-bounds$ ./build/div
-------------------
Test bounded positive / unbounded Div
proved
Operation: [ a0 >= 0, a1 ] / [ _, _ ]
 = [ (- a1), a1 ]
Checking lower bound tightness... Tight.
Checking upper bound tightness... Tight.
-------------------
...
```


# Bugs
The `bugs/` subdirectory has `z3` proofs of the bugs that we have verified and changed in the [Halide codebase](https://github.com/halide/Halide). These executables are also built by the `cmake` command described above, and can be executed like so:

```
dev@host:~/verify-bounds$ ./build/mod-check 
-------------------
Test <any> % bounded unsigned Mod
 NOT tight.
-------------------
```
This check confirmed that a particular special case of unsiged modulo was not a tight bound (i.e. no two values in the provided intervals could be combined to produce the maximum value of the resultant bound).