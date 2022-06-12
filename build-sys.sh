#!/bin/bash

set -x

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

file="ruby-$(rbconfig RUBY_API_VERSION)-$(target_arch)-$(target_vendor)-$(target_os).rs"

bindgen \
  ruby_sys.h \
  -o "$file" \
  --allowlist-file ".*/ruby(/.+)?\.h" \
  --blocklist-file ".*/(config|missing|thread_native|win32).h" \
  --blocklist-file ".*/(compiler_is|backward)/.*" \
  --blocklist-item "^(_?_?dev_t|blkcnt_t|(__)?uid_t|(__)?gid_t|(__)?nlink_t|(__)?blksize_t|__blkcnt_t|__uint64_t)$" \
  --blocklist-item "^(HAVE_.*|.*_H|PATH_.*|RBIMPL_.*|USE_.*|RGENGC_WB_PROTECTED_.*|SIZEOF_.*)$" \
  --blocklist-item "^(CASEFOLD_FILESYSTEM|RB_NUM_COERCE_FUNCS_NEED_OPID|RUBY_(ATOMIC_GENERIC_MACRO|DEBUG|NDEBUG|UNTYPED_DATA_WARNING|VM)|ST_INDEX_BITS)$" \
  --blocklist-function "ruby_qsort" \
  --blocklist-function "rbimpl_atomic_or" \
  --blocklist-function "rb_vrescue2|rb_vsprintf|rb_str_vcatf|ruby_vsnprintf|rb_enc_vsprintf" \
  --blocklist-type "va_list|__builtin_va_list|__va_list_tag" \
  --blocklist-function "rb_fd_init|rb_fd_term|rb_fd_zero|rb_fd_set|rb_fd_clr|rb_fd_isset|rb_fd_copy|rb_fd_dup|rb_fd_select|rb_thread_fd_select|rb_w32_fd_copy|rb_w32_fd_dup" \
  --blocklist-type "fd_set|rb_fdset_t|__fd_mask" \
  --blocklist-type "stat" \
  --blocklist-function "rb_stat_new" \
  --blocklist-type ".*pthread_.*" \
  --blocklist-function "ruby_posix_signal" \
  --blocklist-item "^(__darwin_dev_t|__darwin_blkcnt_t|__darwin_uid_t|__darwin_ino64_t|__darwin_gid_t|__darwin_blksize_t|__darwin_intptr_t|__darwin_va_list)$" \
  --blocklist-item "^(DOSISH|RUBY_MBCHAR_MAXSIZE|LONG_LONG_VALUE|PRI[douxXs]VALUE|PRI_VALUE_PREFIX|PRI_64_PREFIX|(RUBY_)?FIXNUM_MAX|RUBY_FIXNUM_MIN|RB_RANDOM_PARENT)$" \
  --blocklist-item "^(WORD|DWORD|UINT|UINT_PTR|ULONG_PTR|LONG|WCHAR|HANDLE|_LIST_ENTRY|LIST_ENTRY|_RTL_CRITICAL_SECTION_DEBUG|PRTL_CRITICAL_SECTION_DEBUG|_RTL_CRITICAL_SECTION|RTL_CRITICAL_SECTION|CRITICAL_SECTION|SOCKET)$" \
  --blocklist-item "^(hostent|servent|protoent|sockaddr|tm|timezone|clockid_t|utimbuf|u_short|u_int|u_long|__gnuc_va_list)$" \
  --blocklist-item "^rb_f_notimplement_$" \
  --blocklist-function "rb_varargs_bad_length" \
  --blocklist-type "ruby_econv_flag_type" \
  --raw-line "#![allow(missing_docs)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(clippy::upper_case_acronyms)]" \
  --default-enum-style rust \
  --no-layout-tests \
  --no-doc-comments \
  -- \
  -I$(rbconfig rubyhdrdir) \
  -I$(rbconfig rubyarchhdrdir) \
  -fdeclspec

rustc --crate-name ruby --edition=2021 "$file" --crate-type lib --emit mir -o /dev/null
