;;; SPDX-FileCopyrightText: 2021 Wolfgang Corcoran-Mathe <wcm@sigwinch.xyz>
;;;
;;; SPDX-License-Identifier: MIT

;;; Generic test framework using SRFI 64.
(import (srfi 1)
        (srfi 128)
        (srfi 189)
        (srfi 64)
        (srfi 224))

(include "test-body.scm")
