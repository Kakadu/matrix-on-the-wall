(lang dune 2.7)

(cram enable)

(generate_opam_files true)

(source
 (github Kakadu/matrix-on-the-wall))

(license LGPL-3.0-only)

(authors "Kakadu")

(maintainers "kakadu@pm.me")

(name matrix-on-the-wall)

(package
 (name matrix-on-the-wall)
 (synopsis
  "Multidimensional matrices with a little bit of relational programming")
 (description "TODO")
 (depends OCanren OCanren-ppx ppx_inline_test ppx_fail))
