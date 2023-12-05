#
# Usage:
#
# ## Building
#
# ```
# nix build
# ```
# Currently there is an issue about scripts not being found.
#
# ## Development shell:
#
# Install `direnv`. Create a `.envrc` file in the project root directory and add
# the line `use flake`:
# ```sh
# echo "use flake" > .envrc
# direnv allow
# ```
# This drops the shell into a development environment with all dependencies
# installed.
{
  description = "cvc5";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-23.11";
    flake-parts.url = "github:hercules-ci/flake-parts";
    cadical = {
      url = "github:arminbiere/cadical";
      flake = false;
    };
    symFPU = {
      url = "github:martin-cs/symfpu/e6ac3af9c2c574498ea171c957425b407625448b";
      flake = false;
    };
  };

  outputs = inputs @ {
    self,
    nixpkgs,
    flake-parts,
    cadical,
    symFPU,
    ...
  } : flake-parts.lib.mkFlake { inherit inputs; } {
    flake = {
    };
    systems = [
      "x86_64-linux"
      "x86_64-darwin"
    ];
    perSystem = { system, pkgs, ... }: let
      cadical' = pkgs.stdenv.mkDerivation {
        name = "CaDiCaL";
        src = cadical;
        enableParallelBuilding = true;
        configurePhase = ''
          sh configure
        '';
        installPhase = ''
          mkdir -p $out/bin $out/lib $out/include
          cp build/libcadical.a $out/lib/
          cp src/cadical.hpp $out/include/
          cp build/cadical $out/bin/
          cp build/mobical $out/bin/
        '';
      };
      symFPU' = pkgs.stdenv.mkDerivation {
        name = "SymFPU";
        src = symFPU;
        dontConfigure = true;
        dontBuild = true;
        installPhase = ''
          mkdir -p $out/symfpu
          cp -r core $out/symfpu/
          cp -r utils $out/symfpu/
        '';
      };
      paths = {
        CaDiCaL_LIBRARIES = "${cadical'}/lib";
        CaDiCaL_INCLUDE_DIR = "${cadical'}/include";
        SymFPU_INCLUDE_DIR = "${symFPU}/include";
      };
      # Needed for the built executable and dev shell
      common = [
        pkgs.cmake
        pkgs.gmp
        pkgs.python310
        pkgs.python310Packages.tomli
        pkgs.python310Packages.pyparsing
        cadical' symFPU'
      ];
      # Main build target
      cvc5 = pkgs.stdenv.mkDerivation ({
        name = "cvc5";
        src = ./.;
        buildInputs = common ++ [pkgs.bash];
        enableParallelBuilding = true;
        dontUseCmakeConfigure = true;
        configurePhase = ''
          echo "Configure phase pwd: $PWD"
          bash configure.sh --no-poly
        '';
        buildPhase = ''
          cd build
          make
        '';
        installPhase = ''
          mkdir -p $out/bin
          cp build/bin/* $out/bin/
        '';
      } // paths);
    in rec {
      packages = {
        default = cvc5;
      };
      devShells.default = pkgs.mkShell ({
        buildInputs = common;
      } // paths);
    };
  };
}
