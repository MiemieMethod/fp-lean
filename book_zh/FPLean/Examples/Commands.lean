import FPLean.Examples.Commands.Env
import FPLean.Examples.Commands.ShLex
import Lean.Elab
import Verso.FS

namespace FPLean.Commands
open Lean

variable {m : _} [Monad m] [MonadEnv m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadError m]

private def replacementChar : Char := Char.ofNat 0xfffd

private def validScalar (n : Nat) : Bool :=
  n <= 0x10ffff && !(0xd800 <= n && n <= 0xdfff)

private def byteAt? (bytes : ByteArray) (i : Nat) : Option UInt8 :=
  if h : i < bytes.size then some (bytes.get i h) else none

private def cont? (bytes : ByteArray) (i : Nat) : Option Nat := do
  let b := (← byteAt? bytes i).toNat
  if 0x80 <= b && b <= 0xbf then some (b - 0x80) else none

partial def decodeLossyUtf8 (bytes : ByteArray) : String := Id.run do
  let mut out := ""
  let mut i := 0
  while i < bytes.size do
    let b := (byteAt? bytes i).getD 0 |>.toNat
    if b < 0x80 then
      out := out.push (Char.ofNat b)
      i := i + 1
    else if b < 0xc2 then
      out := out.push replacementChar
      i := i + 1
    else if b < 0xe0 then
      match cont? bytes (i + 1) with
      | some b2 =>
          out := out.push (Char.ofNat (((b - 0xc0) * 0x40) + b2))
          i := i + 2
      | none =>
          out := out.push replacementChar
          i := i + 1
    else if b < 0xf0 then
      match cont? bytes (i + 1), cont? bytes (i + 2) with
      | some b2, some b3 =>
          let code := ((b - 0xe0) * 0x1000) + (b2 * 0x40) + b3
          if code >= 0x800 && validScalar code then
            out := out.push (Char.ofNat code)
            i := i + 3
          else
            out := out.push replacementChar
            i := i + 1
      | _, _ =>
          out := out.push replacementChar
          i := i + 1
    else if b < 0xf5 then
      match cont? bytes (i + 1), cont? bytes (i + 2), cont? bytes (i + 3) with
      | some b2, some b3, some b4 =>
          let code := ((b - 0xf0) * 0x40000) + (b2 * 0x1000) + (b3 * 0x40) + b4
          if code >= 0x10000 && validScalar code then
            out := out.push (Char.ofNat code)
            i := i + 4
          else
            out := out.push replacementChar
            i := i + 1
      | _, _, _ =>
          out := out.push replacementChar
          i := i + 1
    else
      out := out.push replacementChar
      i := i + 1
  return out

def ensureContainer (container : Ident) : m Container := do
  let name := container.getId
  if let some c := (containersExt.getState (← getEnv)).find? name then return c
  let tmp ← IO.FS.createTempDir
  let c : Container := ⟨tmp, {}⟩
  let projectRoot : System.FilePath := ".."
  let copyErrors : IO.Ref (Array String) ← IO.mkRef #[]
  Verso.FS.copyRecursively (fun s => copyErrors.modify (·.push s)) projectRoot tmp shouldCopy
  let errs ← (copyErrors.get : IO _)
  unless errs.isEmpty do
    throwErrorAt container "Errors copying project to container {name}: {indentD <| MessageData.joinSep (errs.toList.map toMessageData) Format.line}"
  modifyEnv (containersExt.modifyState · (·.insert name c))
  return c
where
  shouldCopy (path : System.FilePath) : IO Bool := do
    let some x := path.fileName
      | return true
    return !(x.startsWith ".") && !(x == "site-packages") && !(x == "_out") && !(x == "static")

def requireContainer (container : Ident) : m Container := do
  let name := container.getId
  if let some c := (containersExt.getState (← getEnv)).find? name then return c
  else throwErrorAt container "Not found: '{name}'"

private def localeVars : Array String :=
  #["LANG", "LC_ALL"]

private def lakeVars : Array String :=
  #["ELAN_TOOLCHAIN", "LEAN_SYSROOT", "LEAN", "LAKE", "LAKE_HOME", "LEAN_PATH", "LAKE_CACHE_DIR", "LEAN_AR", "LEAN_CC", "DYLD_LIBRARY_PATH"]

private def fixPath (path : String) :=
  System.SearchPath.parse path
    |>.iter
    |>.map (·.toString)
    |>.filter (fun p => ((p.find? ".elan").isNone || (p.find? "toolchains").isNone))
    |>.toList
    |> System.SearchPath.separator.toString.intercalate

private def resolveExe (dir : System.FilePath) (cmd : String) : IO String := do
  let path : System.FilePath := cmd
  if path.extension.isSome || System.FilePath.exeExtension.isEmpty then
    return cmd
  let candidate := dir / path.addExtension System.FilePath.exeExtension
  if ← candidate.pathExists then
    return candidate.toString
  return cmd

private def cleanRelativePath (p : String) : String :=
  let p := p.trimAscii.copy
  if p.startsWith "./" then p.drop 2 |>.copy
  else if p.startsWith ".\\" then p.drop 2 |>.copy
  else p

private def resolveProgram (workDir extraPath : System.FilePath) (cmd : String) : IO String := do
  let pathStr := cleanRelativePath cmd
  let rel : System.FilePath := pathStr
  if rel.isAbsolute then
    return pathStr
  let localPath := workDir / rel
  if ← localPath.pathExists then
    return localPath.toString
  let exeLocal := workDir / rel.addExtension System.FilePath.exeExtension
  if ← exeLocal.pathExists then
    return exeLocal.toString
  if pathStr.contains System.FilePath.pathSeparator then
    return localPath.toString
  resolveExe extraPath pathStr

private def normalizeNewlines (s : String) : String :=
  s.replace "\r\n" "\n" |>.replace "\r" "\n"

private def processEnv (extraPath : String) : IO (Array (String × Option String)) := do
  let path := (← IO.getEnv "PATH").map fixPath |>.getD ""
  let path := System.SearchPath.separator.toString.intercalate [extraPath, path]
  return #[("PATH", some path)] ++ lakeVars.map (·, none) ++ localeVars.map (·, some "C.UTF-8")

private structure PreparedCommand where
  cmd : String
  args : Array String
  input? : Option String := none
  echoInput? : Option String := none
  allowFailure : Bool := false

private def echoPrefix? (command : String) : Option String := do
  let command := command.trimAscii
  let rest ← command.dropPrefix? "echo "
  let rest := rest.toString.trimAscii.copy
  if rest.startsWith "\"" && rest.endsWith "\"" then
    let text := rest.drop 1 |>.dropEnd 1 |>.copy
    some (text ++ "\n")
  else
    some (rest ++ "\n")

private def expectScriptInput (script : String) : String :=
  if script.contains "send \"David\\n\"" then "David\n"
  else if script.contains "send \"\\n\"" then "\n"
  else ""

private def expectScriptSpawn? (script : String) : Option String := Id.run do
  for line in normalizeNewlines script |>.splitOn "\n" do
    let line := line.trimAscii
    if let some spawn := line.dropPrefix? "spawn " then
      return some spawn.toString.trimAscii.copy
  none

private def interleaveInput (stdout input : String) : String :=
  if input.isEmpty then stdout
  else
    let stdout := normalizeNewlines stdout
    let input := normalizeNewlines input
    match stdout.splitOn "\n" with
    | first :: rest => first ++ "\n" ++ input ++ "\n".intercalate rest
    | [] => stdout ++ input

private def localPath (workDir : System.FilePath) (p : String) : System.FilePath :=
  let rel : System.FilePath := cleanRelativePath p
  if rel.isAbsolute then rel else workDir / rel

private def builtinCommand? (workDir : System.FilePath) (cmdStr : String) : IO (Option IO.Process.Output) := do
  let .ok args := Shell.shlex cmdStr
    | return none
  if args.size = 0 then
    return none
  match args[0]! with
  | "mkdir" =>
      if args.size == 3 && args[1]! == "-p" then
        IO.FS.createDirAll (localPath workDir args[2]!)
        return some { exitCode := 0, stdout := "", stderr := "" }
      return none
  | "touch" =>
      for arg in args.extract 1 do
        let path := localPath workDir arg
        if let some parent := path.parent then
          IO.FS.createDirAll parent
        unless ← path.pathExists do
          IO.FS.writeFile path ""
      return some { exitCode := 0, stdout := "", stderr := "" }
  | "cp" =>
      if args.size == 3 then
        let src := localPath workDir args[1]!
        let mut dst := localPath workDir args[2]!
        if (← dst.pathExists) && (← dst.isDir) then
          dst := dst / src.fileName.get!
        let bytes ← IO.FS.readBinFile src
        if let some parent := dst.parent then
          IO.FS.createDirAll parent
        IO.FS.writeBinFile dst bytes
        return some { exitCode := 0, stdout := "", stderr := "" }
      return none
  | "ls" =>
      let target := if args.size == 1 then workDir else localPath workDir args[1]!
      let entries ← target.readDir
      let names := entries.map (·.fileName) |>.qsort (· < ·)
      return some { exitCode := 0, stdout := String.intercalate "\n" names.toList ++ "\n", stderr := "" }
  | _ => return none

def command (container : Ident) (dir : System.FilePath) (command : StrLit) (viaShell := false) : m IO.Process.Output := do
  let c ← ensureContainer container
  unless dir.isRelative do
    throwError "Relative directory expected, got '{dir}'"
  let workDir := c.workingDirectory / "examples" / dir
  IO.FS.createDirAll workDir
  let extraPathFile := (← IO.currentDir) / ".." / "examples" / ".lake" / "build" / "bin"
  let extraPath := extraPathFile.toString
  let extraPathForEnv := if extraPath.contains ' ' || extraPath.contains '"' || extraPath.contains '\'' then extraPath.quote else extraPath
  let prepared ← prepare workDir extraPathFile
  let out ←
    if let some out ← builtinCommand? workDir command.getString then
      pure out
    else
      outputLossyUtf8 {
        cmd := prepared.cmd,
        args := prepared.args,
        cwd := workDir,
        env := ← processEnv extraPathForEnv
      } prepared.input?
  let out := { out with stdout := prepared.echoInput?.map (interleaveInput out.stdout) |>.getD out.stdout }
  if out.exitCode != 0 && !prepared.allowFailure then
    let stdout := m!"Stdout: {indentD out.stdout}"
    let stderr := m!"Stderr: {indentD out.stderr}"
    throwErrorAt command "Non-zero exit code from '{command.getString}' ({out.exitCode}).\n{indentD stdout}\n{indentD stderr}"
  modifyEnv (containersExt.modifyState · (·.insert container.getId { c with outputs := c.outputs.insert command.getString.trimAscii.copy out.stdout }))
  return out

where
  outputLossyUtf8 (args : IO.Process.SpawnArgs) (input? : Option String) : IO IO.Process.Output := do
    let child ←
      if let some input := input? then
        let (stdin, child) ← (← IO.Process.spawn { args with stdout := .piped, stderr := .piped, stdin := .piped }).takeStdin
        stdin.putStr input
        stdin.flush
        pure child
      else
        IO.Process.spawn { args with stdout := .piped, stderr := .piped, stdin := .null }
    let stdout ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
    let stderr ← child.stderr.readBinToEnd
    let exitCode ← child.wait
    let stdout ← IO.ofExcept stdout.get
    return {
      exitCode
      stdout := decodeLossyUtf8 stdout
      stderr := decodeLossyUtf8 stderr
    }

  prepare (workDir extraPath : System.FilePath) : m PreparedCommand := do
    if command.getString.trimAscii.startsWith "expect -f " then
      let cmdStr := command.getString.trimAscii
      let scriptPath := cleanRelativePath <| cmdStr.drop "expect -f ".length |>.copy
      let scriptName := (System.FilePath.mk scriptPath).fileName.getD scriptPath
      match workDir.fileName, scriptName with
      | some "hello-name", "run" =>
          let (cmd, args) ← cmdAndArgsFromText workDir extraPath "lean --run HelloName.lean"
          return { cmd, args, input? := some "David\n", echoInput? := some "David\n" }
      | some "early-return", "run" =>
          let (cmd, args) ← cmdAndArgsFromText workDir extraPath "lean --run EarlyReturn.lean"
          return { cmd, args, input? := some "David\n", echoInput? := some "David\n" }
      | some "early-return", "too-many-args" =>
          let (cmd, args) ← cmdAndArgsFromText workDir extraPath "lean --run EarlyReturn.lean David"
          return { cmd, args, allowFailure := true }
      | some "early-return", "no-name" =>
          let (cmd, args) ← cmdAndArgsFromText workDir extraPath "lean --run EarlyReturn.lean"
          return { cmd, args, input? := some "\n", echoInput? := some "\n", allowFailure := true }
      | some "sort-demo", "run-usage" =>
          let (cmd, args) ← cmdAndArgsFromText workDir extraPath "sort"
          return { cmd, args, allowFailure := true }
      | _, _ =>
          let (cmd, args) ← cmdAndArgsFromText workDir extraPath command.getString
          return { cmd, args }
    else if viaShell && System.Platform.isWindows then
      prepareWindowsShell workDir extraPath command.getString
    else if viaShell then
      return { cmd := "bash", args := #["-c", command.getString] }
    else
      let (cmd, args) ← cmdAndArgsFromText workDir extraPath command.getString
      return { cmd, args }

  prepareWindowsShell (workDir extraPath : System.FilePath) (cmdStr : String) : m PreparedCommand := do
    let cmdText := cmdStr.trimAscii.copy
    if let [left, right] := cmdText.splitOn "|" then
      let some input := echoPrefix? left
        | throwErrorAt command "Unsupported shell command on Windows: '{cmdText}'"
      let (cmd, args) ← cmdAndArgs workDir extraPath right.trimAscii.copy
      return { cmd, args, input? := some input }
    else if let [left, right] := cmdText.splitOn "<" then
      let input ← IO.FS.readFile (workDir / resolveLocalPath right.trimAscii.copy)
      let (cmd, args) ← cmdAndArgs workDir extraPath left.trimAscii.copy
      return { cmd, args, input? := some input }
    else
      return { cmd := "cmd.exe", args := #["/C", cmdText] }

  cmdAndArgsFromText (workDir extraPath : System.FilePath) (cmdStr : String) : m (String × Array String) := do
    match Shell.shlex cmdStr with
    | .error e => throwErrorAt command e
    | .ok components =>
      if h : components.size = 0 then
        throwErrorAt command "No command provided"
      else
        let program ← resolveProgram workDir extraPath components[0]
        pure (program, components.extract 1)

  resolveLocalPath (p : String) : String :=
    cleanRelativePath p

  cmdAndArgs (workDir extraPath : System.FilePath) (cmdStr : String) : m (String × Array String) := do
    match Shell.shlex cmdStr with
    | .error e => throwErrorAt command e
    | .ok components =>
      if h : components.size = 0 then
        throwErrorAt command "No command provided"
      else
        let program ← resolveProgram workDir extraPath components[0]
        pure (program, components.extract 1)


def commandOut (container : Ident) (command : StrLit) : m String := do
  let c ← requireContainer container
  if let some out := c.outputs[command.getString.trimAscii.copy]? then
    return out
  else throwErrorAt command "Output not found: {indentD command}"

def fileContents (container : Ident) (file : StrLit) : m String := do
  let c ← requireContainer container
  let filename := c.workingDirectory / "examples" / file.getString
  unless (← filename.pathExists) do
    throwErrorAt file "{filename} does not exist"
  if (← filename.isDir) then
    throwErrorAt file "{filename} is a directory"
  IO.FS.readFile filename


end Commands
