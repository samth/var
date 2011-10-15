#lang var ;trace
(module foo racket (provide/contract [foo ((nat? -> nat?) -> nat?)]))
(module addone racket (require) (define (addone n) (add1 n)) (provide/contract [addone (nat? -> nat?)]))
(require (only-in foo foo) (only-in addone addone))
(foo addone)