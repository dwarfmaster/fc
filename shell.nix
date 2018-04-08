{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc802" }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, array, base, containers, mtl, stdenv
      , transformers
      }:
      mkDerivation {
        pname = "fc";
        version = "0.1.0.0";
        src = ./.;
        isLibrary = false;
        isExecutable = true;
        executableHaskellDepends = [
          array base containers mtl transformers
        ];
        buildDepends = with pkgs; [ cabal-install ];
        license = stdenv.lib.licenses.mit;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  drv = haskellPackages.callPackage f {};

in

  if pkgs.lib.inNixShell then drv.env else drv
