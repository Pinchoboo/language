FROM ubuntu:20.04
RUN apt-get update
RUN apt-get install -y git curl llvm-12-dev llvm-12-tools clang-12 build-essential zlib1g-dev
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

#RUN git clone https://github.com/Pinchoboo/language/
COPY / /language

WORKDIR /language
RUN cargo clean
RUN cargo build