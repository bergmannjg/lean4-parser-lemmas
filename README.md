# Lean 4 Parser Lemmas

Some lemmas for [Lean 4 / Parser](https://github.com/fgdorais/lean4-parser).

This project contains specifications for some parsers:

* anyToken,
* lookAhead,
* peek,
* withBacktracking,
* notFollowedBy,
* endOfInput.

There are properties to prove the termination of recursive parsers like Parser.foldr.

These properties depend on classes for Parser.Stream.
Instances are provided for String.Slice and OfList streams.
