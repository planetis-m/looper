
# Looper — for loop macros for Nim

## About
This nimble package contains ``for`` loop macros. This is an expiremental Nim future.
They work like inline iterators - only called from ``for`` loops.

### The `zip` macro

```nim
import looper
let
   a = [1, 3, 5, 7]
   b = @[0, 2, 4, 6, 8]
   c = @["one", "two", "three", "four", "five"]

# It supports variadic arguments of different types,
# each container type must support indexing

for (x, y, z) in zip(a, b, c):
   echo x, " ", y, " ", z

# Also written as:
for x, y, z in zip(a, b, c):
   echo x, " ", y, " ", z

# This is supported too:
for w in zip(a, b, c):
   echo w
```

### The `enumerate` macro

```nim
import looper
let
   a = [1, 3, 5, 7]

for (i, x) in enumerate(a.iter):
   echo i, " ", x

# Also written as:
for i, x in enumerate(a.iter):
   echo i, " ", x
```

### Known quirks
- Nested tuple unpacking ``for (i, (x, y)) in enumerate(iterable)`` is invalid syntax
  you have to write ``for i, (x, y) in enumerate(iterable)`` instead.

- The enumerate macros doesn't support tuples: ``for w in enumerate(iterable)`` this is because of
  the way it is implemented.

### License

This library is distributed under the MIT license. For more information see `copying.txt`.
