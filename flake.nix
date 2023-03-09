{
  description = "agda-unimath";

  inputs = {
    # Unstable is needed for Agda 2.6.3, latest stable 22.11 only has 2.6.2.2
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages."${system}";
          agda = pkgs.agda;
          python = pkgs.python3.withPackages (p: with p; [ requests ]);
        in
        {
          devShells.default = pkgs.mkShell {
            name = "agda-unimath";

            # Build tools
            packages = [
              agda
              # part of `make check`
              pkgs.time
              # update-contributors.py
              python
              # working on the website
              pkgs.mdbook
	      pkgs.mdbook-katex
	      # mdbook-toc is not included here and hence must be installed manually
            ];
          };

          devShell = self.devShells."${system}".default;
        });
}
