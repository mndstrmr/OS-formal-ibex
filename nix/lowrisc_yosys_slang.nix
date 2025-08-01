{
  pkgs,
  src
}:
pkgs.stdenv.mkDerivation (finalAttrs: {
  inherit src;
  pname = "yosys-slang";
  version = "0.0.1";
  buildInputs = with pkgs; [
    yosys
    gcc
    cmake
  ];
  installPhase = ''
    mkdir -p $out/lib
    cp slang.so $out/lib/slang.so
  '';
})
