#!/usr/bin/env perl

use strict ;
BEGIN { push (@INC, "..") }
use Version ;

our $destdir = shift @ARGV ;

print <<"EOF";
# Specifications for the "pa_ppx_hashcons" preprocessor:
version = "$Version::version"
description = "pa_ppx_hashcons deriver"

  requires(toploop) = "camlp5,pa_ppx.deriving_plugins.show"
  archive(toploop) = "pa_deriving_hashcons.cmo"

    requires(syntax,preprocessor) = "camlp5,pa_ppx.deriving_plugins.show"
    archive(syntax,preprocessor,-native) = "pa_deriving_hashcons.cmo"
    archive(syntax,preprocessor,native) = "pa_deriving_hashcons.cmx"

  package "link" (
  requires(byte) = "camlp5,pa_ppx.deriving_plugins.show.link"
  archive(byte) = "pa_deriving_hashcons.cmo"
  )
  requires = "camlp5,pa_ppx.deriving_plugins.show,pa_ppx.runtime"

EOF
