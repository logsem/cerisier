FROM ubuntu:jammy

# Install system packages
RUN apt-get update -yq \
&& apt-get install -yq --no-install-recommends \
   autoconf automake ca-certificates git \
   ocaml-nox opam pkg-config sudo libgmp-dev \
&& apt-get clean \
&& rm -fr /var/lib/apt/lists/*

# Add rocq user and drop root
RUN useradd -lmU -s /bin/bash -G sudo -p '' rocq
WORKDIR /home/rocq
USER rocq

# Install common packages
RUN set -x \
&& opam init -j$(nproc) --compiler 4.14.0 --auto-setup --yes --disable-completion --disable-sandboxing \
&& opam repo add --all-switches --set-default coq-released https://coq.inria.fr/opam/released \
&& opam install -vyj$(nproc) dune num ocamlfind zarith conf-findutils conf-gmp opam-depext \
&& opam clean -acrs --logs \
&& opam config list && opam list

ENTRYPOINT ["opam", "exec", "--"]
CMD ["/bin/bash", "--login"]

# Install coq libraries
RUN opam install -vyj$(nproc) coq-iris=4.1.0 coq-equations=1.3+8.18 \
&& opam clean -acrs --logs \
&& opam config list && opam list

# Clone artifact repository
RUN git clone --depth=1 https://github.com/logsem/cerisier.git
WORKDIR cerisier
RUN git submodule update --init --recursive


