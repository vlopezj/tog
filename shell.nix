let 
    pkgs = (import <nixpkgs> {});
    haskellPackages = pkgs.recurseIntoAttrs (pkgs.haskell.packages.ghc7102.override {
        overrides = self : super :
        let callPackage = self.callPackage;
            dontTest = pkgs.haskell.lib.dontCheck;
        in {
           cabal-install = super.cabal-install; # .override{ enableLibraryProfiling = true; };
           BNFC = dontTest (callPackage (import ./nix/BNFC.nix) {});
           thisPackage = callPackage (import ./default.nix) {};
        };});
in pkgs.stdenv.mkDerivation {
    name = haskellPackages.thisPackage.name;
    buildInputs = 
       [(haskellPackages.ghcWithPackages (hs: ([
         hs.cabal-install
         hs.alex
         hs.happy
         hs.BNFC
       ] ++ haskellPackages.thisPackage.propagatedNativeBuildInputs)))] ++
       [ pkgs.glibcLocales
       ];
    shellHook = ''
      export LANG=en_US.UTF-8
      '';
     }
