{ mkDerivation, alex, array, base, bifunctors, boxes, containers
, either, happy, hashable, hashtables, lens, mtl, nats
, optparse-applicative, profunctors, safe, semigroups, split
, stdenv, tagged, transformers, transformers-compat
, unordered-containers, wl-pprint
}:
mkDerivation {
  pname = "tog";
  version = "0.1.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    array base bifunctors boxes containers either hashable hashtables
    lens mtl nats optparse-applicative profunctors safe semigroups
    split tagged transformers transformers-compat unordered-containers
    wl-pprint
  ];
  libraryToolDepends = [ alex happy ];
  executableHaskellDepends = [ base ];
  license = stdenv.lib.licenses.bsd3;
}
