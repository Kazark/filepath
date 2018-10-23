module Path

%default total
%access public export

validNameChar : Char -> Maybe Char
validNameChar c =
  if c < ' ' || c == '\DEL' || c == '/' || c == '\\' || c == ':'
  then Nothing
  else Just c

||| There are characters that we want to block from a file path, whether because
||| they are not supported in the underlying filesystem, or just because it is
||| ridiculous or inconvenient to have them in file paths, even if they were in
||| the underlying filesystem. Now we could do this by constructing elaborate
||| proofs that our characters were only in a certain subset of what they could
||| be; but this sounds like an incredibly heavyweight, unweildy thing to do
||| when we are dealing at the level of an individual character within a much
||| larger string-like object! Instead, then, we exploit the idea of
||| isomorphisms between normal forms: that is, we want to construct our
||| parser-printer such that there is a one-to-one match between the normal form
||| of a path in the syntax, and its normal form in our conceptual model. The
||| ability to speak of normal forms is what frees us to not have to construct
||| such proofs: instead, we simply allow the conceptual model to have multiple
||| characters normalize to only one character that we want in our target subset
||| of path characters. This gives us a way to sane, consistent way to handle
||| illegal characters, without having to actually use the type system to blot
||| them out of existence.
|||
||| An advantage of this approach is that it is portable to languages that do
||| not have dependent types, without the need to introduce opaque types (types
||| with private constructors). A potential disadvantage in the abstract is the
||| imposition of the need for normalization; however, this imposition is not
||| such a great disadvantage in this case, since due to `.` and `..` the
||| standard syntax for filepaths is already subject to this complexity.
|||
||| We choose to normalize a character in a path name by mapping illegal
||| characters and `.` to `_`. `.` is not considered an illegal character since
||| it is allowed in the syntax; but in the conceptual model it is not encoded
||| as a character directly, and therefore for our purposes here must be
||| remapped.
normalizeNameChar : Char -> Char
normalizeNameChar '.' = '_'
normalizeNameChar c = fromMaybe '_' $ validNameChar c

||| Path segment separator: `\` or `/`
data PathSegSep = Backslash | Slash

pathSegSep : PathSegSep -> Char
pathSegSep Backslash = '\\'
pathSegSep Slash = '/'
