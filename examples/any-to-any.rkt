#lang var rho eval

(module m racket
  (provide/contract [f (-> any/c any/c)]))

(require 'm)
(f f)
