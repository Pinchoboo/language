# MPL prototype
Compiler and some example programs in MPL. 

The rust source code is spaghetti without comments.

check out [all features](examples/all_features.mpl)
# Requirements
cargo and the following packages: llvm-12-dev llvm-12-tools clang-12 build-essential zlib1g-dev


# Usage
cargo run -- path/to/file.mpl

to run the benchmarks run: 
1. cargo test
2. cargo test --features heapsize

# Troubleshooting
1. cargo clean