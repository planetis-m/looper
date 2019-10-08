import macros
{.experimental: "forLoopMacros".}

macro zip*(x: ForLoopStmt): untyped =
   expectKind x, nnkForStmt
   result = newStmtList()
   let zipArgs = newNimNode(nnkBracket)
   for i in 1 ..< x[^2].len: # zip(a, b, ...)
      zipArgs.add x[^2][i]
   let iterVars = newNimNode(nnkBracket)
   if x.len == 3: # single iteration variable
      if x[0].kind == nnkVarTuple: # for (x, y, ...) in iter
         for i in 0 .. x[0].len-2:
            iterVars.add x[0][i]
         if zipArgs.len != iterVars.len:
            error("Not as many iterator variables and zip arguments")
      else:
         iterVars.add x[0] # for x in iter
   else: # for x, y, ... in iter
      for i in 0 .. x.len-3:
         iterVars.add x[i]
      if zipArgs.len != iterVars.len:
         error("Not as many iterator variables and zip arguments")
   # write: let m = min(len(a), min(len(b), ...))
   let minLen = genSym(nskLet, "m")
   let minArgs = newNimNode(nnkBracket)
   for i in 0 ..< zipArgs.len:
      minArgs.add newCall("len", zipArgs[i])
   result.add newLetStmt(minLen, nestList(bindSym"min", minArgs))
   let indVar = genSym(nskForVar, "i")
   let letSec = newNimNode(nnkLetSection)
   if iterVars.len == 1:
      # write: let x = (a[i], b[i], ...)
      let value = newNimNode(nnkTupleConstr)
      for i in 0 ..< zipArgs.len:
         value.add nnkBracketExpr.newTree(zipArgs[i], indVar)
      letSec.add newIdentDefs(iterVars[0], newEmptyNode(), value)
   else:
      # write: let x = a[i]; let y = b[i]; ...
      for i in 0 ..< iterVars.len:
         let value = nnkBracketExpr.newTree(zipArgs[i], indVar)
         letSec.add newIdentDefs(iterVars[i], newEmptyNode(), value)
   var body = x[^1]
   if body.kind != nnkStmtList:
      body = newTree(nnkStmtList, body)
   body.insert(0, letSec)
   # write: for i in 0 ..< m
   let newFor = nnkForStmt.newTree(indVar,
      nnkInfix.newTree(bindSym"..<", newLit(0), minLen))
   newFor.add body
   result.add newFor

macro enumerate*(x: ForLoopStmt): untyped =
   expectKind x, nnkForStmt
   # we strip off the first for loop variable and use
   # it as an integer counter:
   result = newStmtList()
   var body = x[^1]
   if body.kind != nnkStmtList:
      body = newTree(nnkStmtList, body)
   var newFor = newTree(nnkForStmt)
   if x.len == 3: # single iteration variable
      if x[0].kind == nnkVarTuple: # for (x, y, ...) in iter
         result.add newVarStmt(x[0][0], newLit(0))
         body.add newCall(bindSym"inc", x[0][0])
         for i in 1 .. x[0].len-2:
            newFor.add x[0][i]
      else:
         error("enumerate iterator doesn't support tuples") # for x in iter
   else: # for x, y, ... in iter
      result.add newVarStmt(x[0], newLit(0))
      body.add newCall(bindSym"inc", x[0])
      for i in 1 .. x.len-3:
         newFor.add x[i]
   # transform enumerate(X) to 'X'
   newFor.add x[^2][1]
   newFor.add body
   result.add newFor
   # now wrap the whole macro in a block to create a new scope
   result = newBlockStmt(result)

when isMainModule:
   let
      a = [1, 3, 5, 7]
      b = @[0, 2, 4, 6, 8]
      c = @["one", "two", "three", "four", "five"]

   block:
      var res: seq[(int,)]
      for x in zip(a):
         res.add x
      assert res == @[(1,), (3,), (5,), (7,)]

   block:
      var res: seq[(int, int, int)]
      for (x, y, z) in zip(a, b, @[-1, -2, -3, -4, -5]):
         res.add (x, y, z)
      assert res == @[(1, 0, -1), (3, 2, -2), (5, 4, -3), (7, 6, -4)]

   block:
      var res: seq[(int, int)]
      for x in zip(b, a):
         res.add x
      assert res == @[(0, 1), (2, 3), (4, 5), (6, 7)]

   block:
      var res: seq[(int, int)]
      for x, y in zip(a, b):
         res.add (y, x)
      assert res == @[(0, 1), (2, 3), (4, 5), (6, 7)]

   block:
      var res: seq[(int, int, string)]
      for (x, y, z) in zip(a, b, c):
         res.add (x, y, z)
      assert res == @[(1, 0, "one"), (3, 2, "two"), (5, 4, "three"), (7, 6, "four")]
