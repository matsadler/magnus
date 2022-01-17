function rbconfig () {
  ruby -e'print RbConfig::CONFIG["'"$1"'"]'
}

function target_arch () {
  val=$(uname -m)
  case "$val" in
    arm64)
      echo aarch64;;
    armv7*)
      echo arm7;;
    *)
      echo "$val";;
  esac
}

function target_vendor () {
  case "$OSTYPE" in
    darwin*)
      echo apple;;
    cygwin)
      echo pc;;
    msys)
      echo pc;;
    *)
      echo unknown;;
  esac
}

function target_os () {
  case "$OSTYPE" in
    darwin*)
      echo darwin;;
    cygwin)
      echo windows-gnu;;
    msys)
      echo windows-gnu;;
    *)
      echo "$OSTYPE";;
  esac
}
