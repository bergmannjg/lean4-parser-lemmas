# Lean 4 Parser Lemmas

Some lemmas for [Lean 4 / Parser](https://github.com/fgdorais/lean4-parser).

There are specifications for some parsers:

* anyToken,
* lookAhead,
* peek,
* withBacktracking,
* notFollowedBy,
* endOfInput.

There are properties to prove the termination of recursive parsers like Parser.foldr.

The properties depend on classes for Parser.Stream.
Instances are given for String.Slice, Substring.Raw and OfList streams.
