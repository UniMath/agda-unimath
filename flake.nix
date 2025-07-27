{
  description = "agda-unimath";

  inputs = {
    # Stable 24.11 has Agda 2.7.0.1
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    flake-utils.url = "github:numtide/flake-utils";
    # We aim to support Python 3.8 as long as Ubuntu 20.24 has LTS,
    # since it ships with that version. Python 3.8 itself is already
    # EOL, so it was dropped from nixpkgs 24.05
    nixpkgs-python.url = "github:NixOS/nixpkgs/nixos-23.11";
    # Nixpkgs with tested versions of mdbook crates;
    # may be removed once we backport new mdbook assets to our
    # modified versions
    nixpkgs-mdbook.url = "github:NixOS/nixpkgs?rev=7fdd1421774a52277fb56d64b26aaf7765e1b3fa";
    mdbook-catppuccin = {
      url = "github:catppuccin/mdBook/v1.2.0";
      inputs.nixpkgs.follows = "nixpkgs-mdbook";
    };
  };

  outputs = { self, nixpkgs, nixpkgs-mdbook, nixpkgs-python, flake-utils, mdbook-catppuccin }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages."${system}";
          pkgs-mdbook = nixpkgs-mdbook.legacyPackages."${system}";
          pkgs-python = nixpkgs-python.legacyPackages."${system}";
          python = pkgs-python.python38.withPackages (p: with p; [
            # Keep in sync with scripts/requirements.txt
            # pre-commit <- not installed as a Python package but as a binary below
            pybtex
            requests
            tomli
            graphviz
          ]);

          agda-unimath-package = { lib, mkDerivation, time }: mkDerivation {
            pname = "agda-unimath";

            # For the version format of unreleased packages, see
            # https://nixos.org/manual/nixpkgs/stable/#sec-package-naming
            version = "unstable-2023-09-05";

            # We can reference the directory since we're using flakes,
            # which copies the version-tracked files into the nix store
            # before evaluation, # so we don't run into the issue with
            # nonreproducible source paths as outlined here:
            # https://nix.dev/recipes/best-practices#reproducible-source-paths
            src = ./.;

            nativeBuildInputs = [ time ];

            buildPhase = ''
              runHook preBuild
              make check
              runHook postBuild
            '';

            meta = with lib; {
              description = "Univalent mathematics in Agda";
              homepage = "https://github.com/UniMath/agda-unimath";
              license = licenses.mit;
              platforms = platforms.unix;
            };
          };
        in
        {
          packages.agda-unimath = pkgs.agdaPackages.callPackage agda-unimath-package { };
          packages.default = self.packages."${system}".agda-unimath;

          devShells.default = pkgs.mkShell {
            name = "agda-unimath";

            # Dependencies for building the library
            inputsFrom = [ self.packages."${system}".agda-unimath ];

            # Development tools
            packages = [
              # maintenance scripts
              python
              # pre-commit checks
              pkgs.pre-commit
              pkgs.nodejs
            ] ++ (with pkgs-mdbook; [
              # working on the website
              mdbook
              mdbook-katex
              mdbook-pagetoc
              mdbook-linkcheck
              mdbook-catppuccin.packages."${system}".default
            ]);
          };
        });
}
