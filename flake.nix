{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };


  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        inherit (pkgs) coqPackages;
      in
        rec {
          packages.default = coqPackages.mkCoqDerivation {
              pname = "cerisier";
              version = "0.0.0";

              coq-version = "8.18";

              src = ./.;

              buildInputs = with coqPackages; [ equations iris stdpp ];

              meta = with pkgs.lib; {
                description = "Cerisier: A Program Logic for Attestation";
                homepage = "https://github.com/logsem/cerisier";
                license = licenses.bsd3;
              };
            };

            devShells.default = pkgs.mkShell (with packages.default; {
              name = pname + "-dev";
              packages = buildInputs ++ [ coqPackages.coq coqPackages.coq-lsp ];
            });
          });
}
