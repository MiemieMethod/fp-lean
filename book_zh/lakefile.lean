import Lake

open System Lake DSL

package book where
  version := v!"0.1.0"
  leanOptions :=
  #[⟨`weak.verso.examples.suggest, true⟩,
    ⟨`weak.linter.verso.manual.headerTags, true⟩,
    ⟨`weak.verso.externalExamples.suppressedNamespaces,
      "A Adding Agh Argh Almost Alt AltPos AndDef AndThen AppendOverloads ApplicativeOptionLaws ApplicativeOptionLaws2 ApplicativeToFunctor Apply Argh AutoImpl B BadUnzip BetterHPlus BetterPlicity Blurble Both Busted C CheckFunctorPair Class Cls Cmp Connectives Cont Ctor D Decide Demo Desugared Details DirTree DirTree.Old DirTree.Readerish DirTree.T Double EEE EarlyReturn Eff Errs Eta Evaluator Even Ex Exercises Explicit ExplicitParens Extra Extras F F1 F2 Fake FakeAlternative FakeCoe FakeExcept FakeFunctor FakeMonad FakeOrElse FakeSeqRight FancyDo FastPos FinDef Finny Fixity Floop ForMIO Foo Foo2 Four FourPointFive Golf Golf' Guard H HelloName1 HelloName2 HelloName3 Huh IdentMonad Impl Improved Inductive Inflexible IterSub L Lawful ListExtras Loops Loops.Cont M MMM Main1 Main2 Main3 Match MatchDef Mine Modify MonadApplicative MonadApplicativeDesugar MonadApplicativeProof1 MonadApplicativeProof2 MonadApplicativeProof3 MonadApplicativeProof4 MonadLaws Monadicish Monads.Err Monads.Option Monads.State Monads.Writer More MoreClear MoreMonadic Mut MyList1 MyList15 MyList3 MyListStuff MyMonadExcept MyMonadLift MySum NRT NT NatLits Nested New NoTac Non Numbering Numbering.Short Old One OneAttempt Oooops Ooops Oops Opt Option OrElse Orders Original Other OverloadedBits OverloadedInt OwnInstances Partial PipelineEx PointStuff ProblematicHPlus Prod Proofs PropStuff Provisional Provisional2 R Ranges Readerish ReallyNoTypes Reorder SameDo SeqCounterexample SeqLeftSugar SeqRightSugar Ser Short St StEx StdLibNoUni Str StructNotation Structed SubtypeDemo SugaryOrElse Sum T TTT Tactical TailRec Temp ThenDoUnless Three Transformed Two U Up UseList VariousTypes Verbose Wak Whatevs WithAndThen WithDo WithFor WithInfix WithMatch WithPattern"⟩]

require verso from git "https://github.com/leanprover/verso.git"@"main"

private def examplePath : System.FilePath := "../examples"

private def lakeVars :=
  #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP", "LAKE_CACHE_DIR",
    "LEAN", "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
    "LEAN_GITHASH",
    "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

private def fixPath (path : System.SearchPath) : String :=
  path |>.map (·.toString) |>.filter (!·.contains ".lake") |> System.SearchPath.separator.toString.intercalate

target patchVersoWindowsLock (pkg) : Unit := Job.async do
  let file := pkg.dir / ".lake" / "packages" / "verso" / "src" / "verso" / "Verso" / "Code" / "External" / "Files.lean"
  unless ← file.pathExists do
    error s!"Verso source file not found: {file}"
  let text ← IO.FS.readFile file
  let text := text.replace "\r\n" "\n"
  let lockedBlock := r#"  let toolchainFile ← IO.FS.Handle.mk toolchainfile .read
  -- Lake tends to get in trouble if used concurrently, so build the Lean code with a lock.
  toolchainFile.lock (exclusive := true)
  try
    runCmd m!"loadModuleContent': building extractor" #["run", "--install", toolchain, "lake", "build", "subverso-extract-mod"]
    runCmd m!"loadModuleContent': building highlighted example" #["run", "--install", toolchain, "lake", "build", "+" ++ mod ++ ":highlighted"]
  finally
    toolchainFile.unlock
"#
  let unlockedBlock := r#"  runCmd m!"loadModuleContent': building extractor" #["run", "--install", toolchain, "lake", "build", "subverso-extract-mod"]
  runCmd m!"loadModuleContent': building highlighted example" #["run", "--install", toolchain, "lake", "build", "+" ++ mod ++ ":highlighted"]
"#
  let dedicatedLockBlock := r#"  let lockFile := projectDir / ".lake" / "verso-examples.lock"
  IO.FS.createDirAll lockFile.parent.get!
  discard <| IO.FS.Handle.mk lockFile .append
  let lockHandle ← IO.FS.Handle.mk lockFile .readWrite
  -- Lake/SubVerso highlighted-example cache files are not safe for concurrent writers on Windows.
  lockHandle.lock (exclusive := true)
  try
    runCmd m!"loadModuleContent': building extractor" #["run", "--install", toolchain, "lake", "build", "subverso-extract-mod"]
    runCmd m!"loadModuleContent': building highlighted example" #["run", "--install", toolchain, "lake", "build", "+" ++ mod ++ ":highlighted"]
  finally
    lockHandle.unlock
"#
  let patched :=
    if text.contains dedicatedLockBlock then text
    else if text.contains lockedBlock then text.replace lockedBlock dedicatedLockBlock
    else if text.contains unlockedBlock then text.replace unlockedBlock dedicatedLockBlock
    else text
  if text != patched then
    IO.FS.writeFile file patched
    logInfo "Patched Verso external example loader to serialize highlighted-example builds on Windows."
  else if text.contains dedicatedLockBlock then
    pure ()
  else
    error s!"Unexpected Verso external example loader; patch no longer applies: {file}"

  let expectFile := pkg.dir / ".lake" / "packages" / "verso" / "src" / "verso" / "Verso" / "ExpectString.lean"
  unless ← expectFile.pathExists do
    error s!"Verso source file not found: {expectFile}"
  let expectText ← IO.FS.readFile expectFile
  let expectText := expectText.replace "\r\n" "\n"
  let expectBefore := r#"def expectStringOrDiff (expected : StrLit) (actual : String)
    (preEq : String → String := id)
    (useLine : String → Bool := fun _ => true) : m (Option MessageData) := do
  let expectedLines := expected.getString.splitOn "\n" |>.filter useLine |>.toArray
  let actualLines := actual.splitOn "\n" |>.filter useLine |>.toArray
"#
  let expectAfter := r#"def expectStringOrDiff (expected : StrLit) (actual : String)
    (preEq : String → String := id)
    (useLine : String → Bool := fun _ => true) : m (Option MessageData) := do
  let expectedLines := expected.getString.splitOn "\n" |>.map (fun s => if s.endsWith "\r" then (s.dropEnd 1).copy else s) |>.filter useLine |>.toArray
  let actualLines := actual.splitOn "\n" |>.map (fun s => if s.endsWith "\r" then (s.dropEnd 1).copy else s) |>.filter useLine |>.toArray
"#
  let expectPatched := expectText.replace expectBefore expectAfter
  let expectBefore2 := r#"def expectString (what : String) (expected : StrLit) (actual : String)
    (preEq : String → String := id)
    (useLine : String → Bool := fun _ => true) : m Bool := do
  let expectedLines := expected.getString.splitOn "\n" |>.filter useLine |>.toArray
  let actualLines := actual.splitOn "\n" |>.filter useLine |>.toArray
"#
  let expectAfter2 := r#"def expectString (what : String) (expected : StrLit) (actual : String)
    (preEq : String → String := id)
    (useLine : String → Bool := fun _ => true) : m Bool := do
  let expectedLines := expected.getString.splitOn "\n" |>.map (fun s => if s.endsWith "\r" then (s.dropEnd 1).copy else s) |>.filter useLine |>.toArray
  let actualLines := actual.splitOn "\n" |>.map (fun s => if s.endsWith "\r" then (s.dropEnd 1).copy else s) |>.filter useLine |>.toArray
"#
  let expectPatched := expectPatched.replace expectBefore2 expectAfter2
  if expectText != expectPatched then
    IO.FS.writeFile expectFile expectPatched
    logInfo "Patched Verso expect-string comparison for CRLF normalization."
  else if expectText.contains "(fun s => if s.endsWith \"\\r\" then (s.dropEnd 1).copy else s)" then
    pure ()
  else
    error s!"Unexpected Verso expect-string helper; patch no longer applies: {expectFile}"

  let domainSearchFile := pkg.dir / ".lake" / "packages" / "verso" / "src" / "verso-search" / "VersoSearch" / "DomainSearch.lean"
  unless ← domainSearchFile.pathExists do
    error s!"Verso source file not found: {domainSearchFile}"
  let domainSearchText ← IO.FS.readFile domainSearchFile
  let domainSearchText := domainSearchText.replace "\r\n" "\n"
  let domainSearchBefore := r#"public def searchBoxCode : Array (String × ByteArray) :=
  (include_bin_dir "../../../static-web/search").filterMap fun (name, contents) =>
    if name.endsWith "domain-mappers.js" then none
    else some (name.dropPrefix "../../../static-web/search/" |>.copy, contents)
"#
  let domainSearchAfter := r#"public def searchBoxCode : Array (String × ByteArray) :=
  (include_bin_dir "../../../static-web/search").filterMap fun (name, contents) =>
    let name := name.replace "\\" "/"
    if name.endsWith "domain-mappers.js" then none
    else some (name.dropPrefix "../../../static-web/search/" |>.copy, contents)
"#
  let domainSearchPatched :=
    if domainSearchText.contains domainSearchAfter then domainSearchText
    else domainSearchText.replace domainSearchBefore domainSearchAfter
  if domainSearchText != domainSearchPatched then
    IO.FS.writeFile domainSearchFile domainSearchPatched
    logInfo "Patched Verso search asset paths for Windows."
  else if domainSearchText.contains domainSearchAfter then
    pure ()
  else
    error s!"Unexpected Verso search asset helper; patch no longer applies: {domainSearchFile}"

  let slugFile := pkg.dir / ".lake" / "packages" / "verso" / "src" / "multi-verso" / "MultiVerso" / "Slug.lean"
  unless ← slugFile.pathExists do
    error s!"Verso source file not found: {slugFile}"
  let slugText ← IO.FS.readFile slugFile
  let slugText := slugText.replace "\r\n" "\n"
  let slugBefore := r#"private def mangle (c : Char) : String :=
  replacements.lookup c |>.getD "___"
where
  replacements : List (Char × String) := [
    ('<', "_LT_"),
    ('>', "_GT_"),
    (';', "_SEMI_"),
    ('‹', "_FLQ_"),
    ('›', "_FRQ_"),
    ('«', "_FLQQ_"),
    ('»', "_FLQQ_"),
    ('⟨', "_LANGLE_"),
    ('⟩', "_RANGLE_"),
    ('(', "_LPAR_"),
    (')', "_RPAR_"),
    ('[', "_LSQ_"),
    (']', "_RSQ_"),
    ('→', "_ARR_"),
    ('↦', "_MAPSTO_"),
    ('⊢', "_VDASH_")
  ]
"#
  let slugAfter := r#"private def hexScalar (n : Nat) : String :=
  let hex := String.ofList (Nat.toDigits 16 n)
  if hex.isEmpty then "0" else hex

private def mangle (c : Char) : String :=
  replacements.lookup c |>.getD s!"_u{hexScalar c.toNat}_"
where
  replacements : List (Char × String) := [
    ('<', "_LT_"),
    ('>', "_GT_"),
    (';', "_SEMI_"),
    ('‹', "_FLQ_"),
    ('›', "_FRQ_"),
    ('«', "_FLQQ_"),
    ('»', "_FLQQ_"),
    ('⟨', "_LANGLE_"),
    ('⟩', "_RANGLE_"),
    ('(', "_LPAR_"),
    (')', "_RPAR_"),
    ('[', "_LSQ_"),
    (']', "_RSQ_"),
    ('→', "_ARR_"),
    ('↦', "_MAPSTO_"),
    ('⊢', "_VDASH_")
  ]
"#
  let slugPatched :=
    if slugText.contains slugAfter then slugText
    else slugText.replace slugBefore slugAfter
  if slugText != slugPatched then
    IO.FS.writeFile slugFile slugPatched
    logInfo "Patched Verso slugs to encode non-ASCII characters."
  else if slugText.contains slugAfter then
    pure ()
  else
    error s!"Unexpected Verso slug helper; patch no longer applies: {slugFile}"
  return ()

input_dir examples where
  path := examplePath
  text := true
  filter := .extension "lean"

input_dir exampleBinaries where
  path := examplePath / ".lake" / "build" / "bin"
  text := false


target buildExamples (pkg) : Unit := Job.async do
  let exs ← examples.fetch
  let exBins ← exampleBinaries.fetch
  let toolchainFile := examplePath / "lean-toolchain"
  let toolchain ← IO.FS.readFile toolchainFile
  let toolchain := toolchain.trimAscii |>.dropPrefix "leanprover/lean4:" |>.dropPrefix "v" |>.copy
  addPureTrace toolchain
  let exFiles ← exs.await
  let exBinFiles ← exBins.await
  for file in exBinFiles do
    if file.extension.isNone || file.extension.isEqSome System.FilePath.exeExtension then
      addTrace (← computeTrace file)
  let mut list := ""
  for file in exFiles do
    addTrace (← computeTrace <| TextFilePath.mk file)
    list := list ++ s!"{file}\n"
  buildFileUnlessUpToDate' (pkg.buildDir / "examples-built") (text := true) do
    Lake.logInfo s!"Building examples in {examplePath}"
    let mut out := ""
    let path := fixPath (← getSearchPath "PATH")
    out := out ++ (← captureProc {
      cmd := "elan",
      args := #["run", "--install", toolchain, "lake", "build"],
      cwd := examplePath,
      env := lakeVars.map (·, none) ++ #[("PATH", some path)]
    })
    IO.FS.createDirAll pkg.buildDir
    IO.FS.writeFile (pkg.buildDir / "examples-built") (list ++ "--- Output ---\n" ++ out)
  return ()

target syncBuildExamples : Unit := do
  .pure <$> (← buildExamples.fetch).await

lean_lib FPLean where
  needs := #[patchVersoWindowsLock, syncBuildExamples]

@[default_target] lean_exe «fp-lean» where root := `Main
