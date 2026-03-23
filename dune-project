(lang dune 3.21)
(name rocq-promising-seq)
(using coq 0.8)

(source (github snu-sf/promising-seq-coq))
(license "BSD-2-Clause")
(authors
  "Minki Cho <minki.cho@sf.snu.ac.kr>"
  "Sung-Hwan Lee <sunghwan.lee@sf.snu.ac.kr>"
  "Jeehoon Kang <jeehoon.kang@sf.snu.ac.kr>"
  "Chung-Kil Hur <gil.hur@sf.snu.ac.kr>"
  "Ori Lahav <ori.lahav@tau.ac.il>"
  "Viktor Vafeiadis <viktor@mpi-sws.org>"
  "Derek Dreyer <dreyer@mpi-sws.org>"
)
(maintainers "yeji.han@sf.snu.ac.kr")

(package
 (name rocq-promising-seq)
 (synopsis "Rocq formalization of the Promising-NA semantics and the SEQ model")
 (depends
  (coq-core (>= 9.0))
  rocq-stdlib
  (coq-sflib (>= 2.1.0))
  (coq-paco (>= 4.2.3))
  (coq-promising-lib (>= 2.1.0))
  (coq-ext-lib (>= 0.13.0))
  (coq-itree (>= 5.2.0))
  (dune (>= 3.21)))
 (maintainers "yeji.han@sf.snu.ac.kr"))
