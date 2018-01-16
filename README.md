About
=====

This is an experimental HTTP framework for Idris. It is not recommended to use this
for production systems yet because of the known issues that still need to be
resolved (see the Known issues section).

See the examples/ directory for example programs that use it.

Installing
========

```idris
git clone git@github.com:A1kmm/http4idris.git
cd http4idris
idris --install http4idris.ipkg
```

Compiling a test program
========================

```idris
cd examples
idris -o Simple -p contrib -p http4idris Simple.idr
```

Known issues and future improvements
====================================

* Idris concurrency uses on OS thread per connection, so performance isn't as high as it could otherwise be.
* The system has no limits on incoming request size, so malicious users can cause unbounded memory usage and memory exhaustion.
* There is no timeout on how long a connection can stay open, which could make it easier to conduct a denial of service attack.
* Idris has a bug in the accept implementation which causes it to crash out occasionally. This Idris PR fixes the issue: https://github.com/idris-lang/Idris-dev/pull/4204
* Idris strings are null terminated and not appropriate for binary data. We should change to some kind of Buffer and let users convert to String.
* The user is currently responsible for ensuring header names, values, and so on don't contain newlines. We could statically guarantee this.
* We should include more tests and property certifications.
