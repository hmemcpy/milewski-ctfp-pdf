FROM nixorg/nix:latest
ENV NIX_PATH="nixpkgs=https://github.com/NixOS/nixpkgs/archive/release-19.03.tar.gz" 
WORKDIR /usr/git
RUN git clone https://github.com/hmemcpy/milewski-ctfp-pdf.git
WORKDIR milewski-ctfp-pdf
RUN nix-shell
