{
  # Libraries
  lib,
  mkRocqDerivation,
  stdenv,

  # Dependencies
  git,
  cvc4,
  cvc5,
  flock,
  python3,
  fetchurl,
  unzip,
  rocq-core,
  rocq-elpi,
  stdlib,
  trakt,
  verit,
  zchaff,

  # Arguments
  version ? null,
}:

let
  case = case: out: { inherit case out; };

  eunoiaPins = builtins.fromJSON (builtins.readFile ../../scripts/eunoia/cvc5-1.4.2.json);
  eunoiaArchive = kind: fetchurl {
    inherit (eunoiaPins.archives.${kind}) url sha256;
  };
  eunoia-toolchain = stdenv.mkDerivation {
    name = "smtrocq-eunoia-cvc5-${eunoiaPins.version}";
    nativeBuildInputs = [ unzip ];
    phases = [ "installPhase" ];
    installPhase = ''
      mkdir -p "$out/downloads" "$out/${eunoiaPins.install_directory}"
      cp ${eunoiaArchive "binary"} "$out/downloads/${eunoiaPins.archives.binary.filename}"
      cp ${eunoiaArchive "source"} "$out/downloads/${eunoiaPins.archives.source.filename}"
      unzip -q ${eunoiaArchive "binary"} -d "$out/${eunoiaPins.install_directory}"
      tar -xzf ${eunoiaArchive "source"} -C "$out/${eunoiaPins.install_directory}" \
        cvc5-cvc5-1.4.2/proofs/eo/cpc
    '';
  };

  lfsc-sigs = stdenv.mkDerivation {
    name = "lfsc-sigs";
    src = ../../src/lfsc/signatures;

    postInstall = ''
      mkdir $out
      cp -rv . $out
    '';
  };
in
mkRocqDerivation rec {
  inherit version;

  owner = "smtcoq";
  pname = "smtcoq";

  opam-name = "rocq-smtcoq";
  useDune = true;

  defaultVersion = lib.switch rocq-core.rocq-version [
    (case (lib.versions.isGt "9.0") "dev")
  ] null;

  release."dev" = {
    hash = null;
    src = lib.cleanSourceWith {
      src = ../..;

      filter =
        path: type:
        let
          name = baseNameOf path;
        in
        (lib.cleanSourceFilter path type && name != "_build")
        && (
          type == "directory"
          || name == "dune"
          || name == "dune.inc"
          || name == "dune-project"
          || builtins.match ".*\\.(v|elpi)$" name != null
          || builtins.match ".*\\.(ml|mli|mll|mly|mlg|mlpack)$" name != null
          || builtins.match ".*\\.(cnf|lfsc|smt2|sh|plf|vtlog|zlog)$" name != null
          || name == "env"
          || builtins.match ".*\\.(py|json|txt|eo|cpc)$" name != null
        );
    };
  };

  propagatedBuildInputs = [
    cvc4
    cvc5
    rocq-core.ocamlPackages.num
    trakt
    verit
    zchaff
  ];

  doCheck = true;
  # The pinned static release is Linux x86-64; keep older PATH solvers for
  # the original backends. Other platforms require their own verified pin.
  EUNOIA_TOOLCHAIN_ROOT = lib.optionalString
    (stdenv.hostPlatform.isLinux && stdenv.hostPlatform.isx86_64) "${eunoia-toolchain}";
  nativeCheckInputs = [ flock python3 ];
  checkPhase = ''
    runHook preCheck
    patchShebangs ./unit-tests/files/run_zchaff.sh
    dune runtest -p ${opam-name} ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
    runHook postCheck
  '';

  passthru = { inherit lfsc-sigs eunoia-toolchain; };

  meta = {
    description = "A Rocq plugin that checks proof witnesses coming from external SAT and SMT solvers";
    homepage = "https://github.com/smtcoq/smtcoq";
    license = lib.licenses.cecill-c;
  };
}
