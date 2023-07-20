{
  description = "agda-unimath";

  inputs = {
    # Unstable is needed for Agda 2.6.3, latest stable 22.11 only has 2.6.2.2
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    mdbook-catppuccin = {
      url = "github:catppuccin/mdBook";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, mdbook-catppuccin }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages."${system}";
          agda = pkgs.agda;
          python = pkgs.python38.withPackages (p: with p; [
            # Keep in sync with scripts/requirements.txt
            requests
          ]);
        in
        {
          devShells.default = pkgs.mkShell {
            name = "agda-unimath";

            # Build tools
            packages = [
              agda
              # part of `make check`
              pkgs.time
              # maintanance scripts
              python
              # working on the website
              pkgs.mdbook
              pkgs.mdbook-katex
              pkgs.mdbook-pagetoc
              pkgs.mdbook-linkcheck
              mdbook-catppuccin.packages."${system}".default
              # pre-commit checks
              pkgs.pre-commit
            ];
          };

          devShell = self.devShells."${system}".default;
        });
}
