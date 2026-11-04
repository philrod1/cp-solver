# Simple CP solver in Rust

For my own learning more than anything else, but hopefully useful 
to include with the VeriPB REPL stuff for end-to-end proovable
solutions.

## The Plan, if you can call it that ...

Implement a few basic constraints/propagators:

 - Linear
 - (In)Equality
 - All Different.  This should be fun.
 - Table.  Probably not going to be fun.

I think I will create my own modelling language where each constraint
 maps directly to a propagator.  If I manage to build something that fits well
with the REPL work, it would be great if the constraints in the
model are directly identifiable in the formula and proof files that
are (hopefully) going to be generated.  I fully plan to at least
take _inspiration_ from MiniZinc ;)

## Why Rust?

I am starting to really like Rust, but the main reason is that Rust
can easily be compiled to WASM (it's just a cargo target), which is
peerfect fo incorporating into the Web version of the VeriPB REPL.

## The Plan

The first order of business for me is to get a feel for the scope of the
project.  I'll do this by laying out the structure of the code before
I start writing any code.  The structure might need to change as I
start implementing stuff, but if it turns out my guesses were wrong,
at least it means I have found a better way.

Next up will be structures and traits.  Also, proof-logging will be
included from the start instead of trying to retrofit it.

## License

Yeah, I guess.  Other VeriPB code uses Apache and MIT, so I will 
likely go with that.
