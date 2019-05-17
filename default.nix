with import <mathcomp_update> {};

stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq ] ++ (with coqPackages; [mathcomp mathcomp-finmap]);
}
  
