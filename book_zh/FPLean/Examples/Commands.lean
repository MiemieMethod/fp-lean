import FPLean.Examples.Commands.Env
import FPLean.Examples.Commands.ShLex
import Lean.Elab
import Verso.FS

namespace FPLean.Commands
open Lean

variable {m : _} [Monad m] [MonadEnv m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadError m]

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
  #["LANG", "LC_ALL", "LC_CTYPE"]

private def lakeVars : Array String :=
  #["ELAN_TOOLCHAIN", "LEAN_SYSROOT", "LEAN", "LAKE", "LAKE_HOME", "LEAN_PATH", "LAKE_CACHE_DIR", "LEAN_AR", "LEAN_CC", "DYLD_LIBRARY_PATH"]

private def fixPath (path : String) :=
  System.SearchPath.parse path
    |>.iter
    |>.map (·.toString)
    |>.filter (fun p => ((p.find? ".elan").isNone || (p.find? "toolchains").isNone))
    |>.toList
    |> System.SearchPath.separator.toString.intercalate

private def gitBashCandidates : Array System.FilePath :=
  #["D:\\Program Files\\Git\\bin\\bash.exe",
    "D:\\Program Files\\Git\\usr\\bin\\bash.exe",
    "C:\\Program Files\\Git\\bin\\bash.exe",
    "C:\\Program Files\\Git\\usr\\bin\\bash.exe",
    "C:\\Program Files (x86)\\Git\\bin\\bash.exe",
    "C:\\Program Files (x86)\\Git\\usr\\bin\\bash.exe"]

private def findBash : IO String := do
  if let some path ← IO.getEnv "FPLEAN_BASH" then
    unless path.trimAscii.isEmpty do
      return path
  for candidate in gitBashCandidates do
    if ← candidate.pathExists then
      return candidate.toString
  return "bash"

private def toBashPath (path : System.FilePath) : String :=
  let path := path.toString.replace "\\" "/"
  match path.toList with
  | drive :: ':' :: rest =>
    s!"/{drive.toLower}/{String.ofList rest}"
  | _ => path

private def shellQuote (s : String) : String :=
  "'" ++ s.replace "'" "'\\''" ++ "'"

def command (container : Ident) (dir : System.FilePath) (command : StrLit) (viaShell := false) : m IO.Process.Output := do
  let c ← ensureContainer container
  unless dir.isRelative do
    throwError "Relative directory expected, got '{dir}'"
  let dir := c.workingDirectory / "examples" / dir
  IO.FS.createDirAll dir
  let extraPath := (← IO.currentDir) / ".." / "examples" / ".lake" / "build" / "bin"
  let (cmd, args) ←
    if viaShell then
      let bash ← findBash
      let script := s!"export PATH={shellQuote (toBashPath extraPath)}:/usr/bin:/bin:/mingw64/bin:\"$PATH\"; {command.getString}"
      pure (bash, #["--noprofile", "--norc", "-c", script])
    else
      cmdAndArgs
  let cmd ←
    if viaShell then
      pure cmd
    else
      let exeSuffix := if System.FilePath.exeExtension.isEmpty then "" else "." ++ System.FilePath.exeExtension
      if exeSuffix.isEmpty || !(cmd.contains '/' || cmd.contains '\\') then
        pure cmd
      else
        let withExt := cmd ++ exeSuffix
        if ← (dir / System.FilePath.mk withExt).pathExists then
          pure withExt
        else
          pure cmd
  let extraPath := extraPath.toString
  let extraPath := if extraPath.contains ' ' || extraPath.contains '"' || extraPath.contains '\'' then extraPath.quote else extraPath
  let path := (← IO.getEnv "PATH").map (System.SearchPath.separator.toString ++ ·) |>.getD ""
  let out ← IO.Process.output {
    cmd := cmd,
    args := args,
    cwd := dir,
    env := #[("PATH", some (extraPath ++ fixPath path)),
             ("PYTHONIOENCODING", some "utf-8"),
             ("LESSCHARSET", some "utf-8")]
           ++ lakeVars.map (·, none)
           ++ localeVars.map (·, some "C.UTF-8")
  }
  if out.exitCode != 0 then
    let stdout := m!"Stdout: {indentD out.stdout}"
    let stderr := m!"Stderr: {indentD out.stderr}"
    throwErrorAt command "Non-zero exit code from '{command.getString}' ({out.exitCode}).\n{indentD stdout}\n{indentD stderr}"
  modifyEnv (containersExt.modifyState · (·.insert container.getId { c with outputs := c.outputs.insert command.getString.trimAscii.copy out.stdout }))
  return out

where
  cmdAndArgs : m (String × Array String) := do
    match Shell.shlex command.getString with
    | .error e => throwErrorAt command e
    | .ok components =>
      if h : components.size = 0 then
        throwErrorAt command "No command provided"
      else
        return (components[0], components.extract 1)


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
