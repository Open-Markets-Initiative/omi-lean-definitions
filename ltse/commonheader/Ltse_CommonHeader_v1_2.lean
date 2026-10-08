import Wire

/-!
# Long-Term Stock Exchange Common Header v1.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LtseCommonheaderTcpV12

/-- Supported Request Mode: one byte code -/
def SupportedRequestMode.codes : List UInt8 :=
  [0x53, 0x52, 0x54]

inductive SupportedRequestMode where
  | stream -- Stream
  | replay -- Replay
  | snapshotMode -- Snapshot Mode
  | unlisted (byte : { byte : UInt8 // byte ∉ SupportedRequestMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SupportedRequestMode

def toByte : SupportedRequestMode → UInt8
  | .stream => 0x53
  | .replay => 0x52
  | .snapshotMode => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SupportedRequestMode :=
  if byte = 0x53 then .stream
  else if byte = 0x52 then .replay
  else .snapshotMode

def ofByte (byte : UInt8) : SupportedRequestMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SupportedRequestMode) : ofByte value.toByte = value := by
  cases value with
  | stream => decide
  | replay => decide
  | snapshotMode => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SupportedRequestMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SupportedRequestMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SupportedRequestMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SupportedRequestMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SupportedRequestMode

/-- Login Reject Code: one byte code -/
def LoginRejectCode.codes : List UInt8 :=
  [0x54, 0x55, 0x56, 0x41]

inductive LoginRejectCode where
  | malformedToken -- Malformed Token
  | tokenTypeUnsupported -- Token Type Unsupported
  | tokenTypeInvalid -- Token Type Invalid
  | authorizationFailed -- Authorization Failed
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginRejectCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginRejectCode

def toByte : LoginRejectCode → UInt8
  | .malformedToken => 0x54
  | .tokenTypeUnsupported => 0x55
  | .tokenTypeInvalid => 0x56
  | .authorizationFailed => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginRejectCode :=
  if byte = 0x54 then .malformedToken
  else if byte = 0x55 then .tokenTypeUnsupported
  else if byte = 0x56 then .tokenTypeInvalid
  else .authorizationFailed

def ofByte (byte : UInt8) : LoginRejectCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginRejectCode) : ofByte value.toByte = value := by
  cases value with
  | malformedToken => decide
  | tokenTypeUnsupported => decide
  | tokenTypeInvalid => decide
  | authorizationFailed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LoginRejectCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LoginRejectCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LoginRejectCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LoginRejectCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LoginRejectCode

/-- Replay Reject Code: one byte code -/
def ReplayRejectCode.codes : List UInt8 :=
  [0x52, 0x41, 0x50, 0x53]

inductive ReplayRejectCode where
  | replayRequestsAreNotAllowed -- Replay Requests Are Not Allowed
  | replayAllRequestsAreNotAllowed -- Replay All Requests Are Not Allowed
  | notTheActiveSession -- Not The Active Session
  | sequenceNumberOutOfRange -- Sequence Number Out Of Range
  | unlisted (byte : { byte : UInt8 // byte ∉ ReplayRejectCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReplayRejectCode

def toByte : ReplayRejectCode → UInt8
  | .replayRequestsAreNotAllowed => 0x52
  | .replayAllRequestsAreNotAllowed => 0x41
  | .notTheActiveSession => 0x50
  | .sequenceNumberOutOfRange => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReplayRejectCode :=
  if byte = 0x52 then .replayRequestsAreNotAllowed
  else if byte = 0x41 then .replayAllRequestsAreNotAllowed
  else if byte = 0x50 then .notTheActiveSession
  else .sequenceNumberOutOfRange

def ofByte (byte : UInt8) : ReplayRejectCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReplayRejectCode) : ofByte value.toByte = value := by
  cases value with
  | replayRequestsAreNotAllowed => decide
  | replayAllRequestsAreNotAllowed => decide
  | notTheActiveSession => decide
  | sequenceNumberOutOfRange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReplayRejectCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReplayRejectCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReplayRejectCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReplayRejectCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReplayRejectCode

/-- Stream Reject Code: one byte code -/
def StreamRejectCode.codes : List UInt8 :=
  [0x52, 0x50, 0x53]

inductive StreamRejectCode where
  | streamRequestsAreNotAllowed -- Stream Requests Are Not Allowed
  | notTheActiveSession -- Not The Active Session
  | sequenceNumberOutOfRange -- Sequence Number Out Of Range
  | unlisted (byte : { byte : UInt8 // byte ∉ StreamRejectCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StreamRejectCode

def toByte : StreamRejectCode → UInt8
  | .streamRequestsAreNotAllowed => 0x52
  | .notTheActiveSession => 0x50
  | .sequenceNumberOutOfRange => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StreamRejectCode :=
  if byte = 0x52 then .streamRequestsAreNotAllowed
  else if byte = 0x50 then .notTheActiveSession
  else .sequenceNumberOutOfRange

def ofByte (byte : UInt8) : StreamRejectCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StreamRejectCode) : ofByte value.toByte = value := by
  cases value with
  | streamRequestsAreNotAllowed => decide
  | notTheActiveSession => decide
  | sequenceNumberOutOfRange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StreamRejectCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StreamRejectCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StreamRejectCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StreamRejectCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StreamRejectCode

/-- Login Request Message: 2 bytes -/
structure LoginRequestMessage where
  tokenType : Alpha 1
  token : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRequestMessage

def encode (message : LoginRequestMessage) : List UInt8 :=
  Alpha.encode message.tokenType
    ++ (Alpha.encode message.token)

def decode (bytes : List UInt8) : Option (LoginRequestMessage × List UInt8) := do
  let (tokenType, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 1 bytes
  pure ({ tokenType, token }, bytes)

@[simp] theorem encode_length (message : LoginRequestMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestMessage

/-- Replay Request Message: 20 bytes -/
structure ReplayRequestMessage where
  sessionId : BitVec 64
  nextSequenceNumber : BitVec 64
  count : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayRequestMessage

def encode (message : ReplayRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.nextSequenceNumber
    ++ (encodeUInt 4 message.count))

def decode (bytes : List UInt8) : Option (ReplayRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (count, bytes) ← decodeUInt 4 bytes
  pure ({ sessionId, nextSequenceNumber, count }, bytes)

@[simp] theorem encode_length (message : ReplayRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ReplayRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayRequestMessage

/-- Replay All Request Message: 8 bytes -/
structure ReplayAllRequestMessage where
  sessionId : BitVec 64
  deriving DecidableEq, Repr

namespace ReplayAllRequestMessage

def encode (message : ReplayAllRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId

def decode (bytes : List UInt8) : Option (ReplayAllRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  pure ({ sessionId }, bytes)

@[simp] theorem encode_length (message : ReplayAllRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ReplayAllRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayAllRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayAllRequestMessage

/-- Stream Request Message: 16 bytes -/
structure StreamRequestMessage where
  sessionId : BitVec 64
  nextSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StreamRequestMessage

def encode (message : StreamRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.nextSequenceNumber)

def decode (bytes : List UInt8) : Option (StreamRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ sessionId, nextSequenceNumber }, bytes)

@[simp] theorem encode_length (message : StreamRequestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StreamRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StreamRequestMessage

/-- Sbe Message -/
structure SbeMessage where
  templateId : BitVec 8
  schemaId : BitVec 8
  version : BitVec 16
  payload : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace SbeMessage

def encode (message : SbeMessage) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) message.payload.val.length)
    ++ (encodeUInt 1 message.templateId
    ++ (encodeUInt 1 message.schemaId
    ++ (encodeUInt 2 message.version
    ++ (encodeMany Byte.encode message.payload.val))))

def decode (bytes : List UInt8) : Option (SbeMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUInt 2 bytes
  let (templateId, bytes) ← decodeUInt 1 bytes
  let (schemaId, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 2 bytes
  let (payload_, bytes) ← decodeMany Byte.decode blockLength.toNat bytes
  if fits_payload : payload_.length < 256 ^ 2 then
    pure ({ templateId, schemaId, version, payload := ⟨payload_, fits_payload⟩ }, bytes)
  else none

theorem encode_length_pos (message : SbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SbeMessage) : (encode message).length ≤ 65541 := by
  have bound_payload := message.payload.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : SbeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.payload.length_lt]
  rfl

end SbeMessage

/-- Unsequenced Message -/
structure UnsequencedMessage where
  sbeMessage : SbeMessage
  deriving DecidableEq, Repr

namespace UnsequencedMessage

def encode (message : UnsequencedMessage) : List UInt8 :=
  SbeMessage.encode message.sbeMessage

def decode (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) := do
  let (sbeMessage, bytes) ← SbeMessage.decode bytes
  pure ({ sbeMessage }, bytes)

theorem encode_length_pos (message : UnsequencedMessage) : (encode message).length > 0 := by
  have positive := SbeMessage.encode_length_pos message.sbeMessage
  unfold encode
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 65541 := by
  have bound_sbeMessage := SbeMessage.encode_length_le message.sbeMessage
  unfold encode
  omega

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SbeMessage.decode_encode, some_bind]
  rfl

end UnsequencedMessage

/-- Login Accepted Message: 1 bytes -/
structure LoginAcceptedMessage where
  supportedRequestMode : SupportedRequestMode
  deriving DecidableEq, Repr

namespace LoginAcceptedMessage

def encode (message : LoginAcceptedMessage) : List UInt8 :=
  SupportedRequestMode.encode message.supportedRequestMode

def decode (bytes : List UInt8) : Option (LoginAcceptedMessage × List UInt8) := do
  let (supportedRequestMode, bytes) ← SupportedRequestMode.decode bytes
  pure ({ supportedRequestMode }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [SupportedRequestMode.encode_length]

theorem encode_length_pos (message : LoginAcceptedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SupportedRequestMode.decode_encode, some_bind]
  rfl

end LoginAcceptedMessage

/-- Login Rejected Message: 1 bytes -/
structure LoginRejectedMessage where
  loginRejectCode : LoginRejectCode
  deriving DecidableEq, Repr

namespace LoginRejectedMessage

def encode (message : LoginRejectedMessage) : List UInt8 :=
  LoginRejectCode.encode message.loginRejectCode

def decode (bytes : List UInt8) : Option (LoginRejectedMessage × List UInt8) := do
  let (loginRejectCode, bytes) ← LoginRejectCode.decode bytes
  pure ({ loginRejectCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [LoginRejectCode.encode_length]

theorem encode_length_pos (message : LoginRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [LoginRejectCode.decode_encode, some_bind]
  rfl

end LoginRejectedMessage

/-- Start Of Session Message: 8 bytes -/
structure StartOfSessionMessage where
  sessionId : BitVec 64
  deriving DecidableEq, Repr

namespace StartOfSessionMessage

def encode (message : StartOfSessionMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId

def decode (bytes : List UInt8) : Option (StartOfSessionMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  pure ({ sessionId }, bytes)

@[simp] theorem encode_length (message : StartOfSessionMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : StartOfSessionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfSessionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfSessionMessage

/-- Replay Begin Message: 12 bytes -/
structure ReplayBeginMessage where
  nextSequenceNumber : BitVec 64
  pendingMessageCount : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayBeginMessage

def encode (message : ReplayBeginMessage) : List UInt8 :=
  encodeUInt 8 message.nextSequenceNumber
    ++ (encodeUInt 4 message.pendingMessageCount)

def decode (bytes : List UInt8) : Option (ReplayBeginMessage × List UInt8) := do
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (pendingMessageCount, bytes) ← decodeUInt 4 bytes
  pure ({ nextSequenceNumber, pendingMessageCount }, bytes)

@[simp] theorem encode_length (message : ReplayBeginMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ReplayBeginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayBeginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayBeginMessage

/-- Replay Rejected Message: 1 bytes -/
structure ReplayRejectedMessage where
  replayRejectCode : ReplayRejectCode
  deriving DecidableEq, Repr

namespace ReplayRejectedMessage

def encode (message : ReplayRejectedMessage) : List UInt8 :=
  ReplayRejectCode.encode message.replayRejectCode

def decode (bytes : List UInt8) : Option (ReplayRejectedMessage × List UInt8) := do
  let (replayRejectCode, bytes) ← ReplayRejectCode.decode bytes
  pure ({ replayRejectCode }, bytes)

@[simp] theorem encode_length (message : ReplayRejectedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ReplayRejectCode.encode_length]

theorem encode_length_pos (message : ReplayRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ReplayRejectCode.decode_encode, some_bind]
  rfl

end ReplayRejectedMessage

/-- Replay Complete Message: 8 bytes -/
structure ReplayCompleteMessage where
  messageCount : BitVec 64
  deriving DecidableEq, Repr

namespace ReplayCompleteMessage

def encode (message : ReplayCompleteMessage) : List UInt8 :=
  encodeUInt 8 message.messageCount

def decode (bytes : List UInt8) : Option (ReplayCompleteMessage × List UInt8) := do
  let (messageCount, bytes) ← decodeUInt 8 bytes
  pure ({ messageCount }, bytes)

@[simp] theorem encode_length (message : ReplayCompleteMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ReplayCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayCompleteMessage

/-- Stream Begin Message: 16 bytes -/
structure StreamBeginMessage where
  nextSequenceNumber : BitVec 64
  maxSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StreamBeginMessage

def encode (message : StreamBeginMessage) : List UInt8 :=
  encodeUInt 8 message.nextSequenceNumber
    ++ (encodeUInt 8 message.maxSequenceNumber)

def decode (bytes : List UInt8) : Option (StreamBeginMessage × List UInt8) := do
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (maxSequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nextSequenceNumber, maxSequenceNumber }, bytes)

@[simp] theorem encode_length (message : StreamBeginMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StreamBeginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamBeginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StreamBeginMessage

/-- Stream Rejected Message: 1 bytes -/
structure StreamRejectedMessage where
  streamRejectCode : StreamRejectCode
  deriving DecidableEq, Repr

namespace StreamRejectedMessage

def encode (message : StreamRejectedMessage) : List UInt8 :=
  StreamRejectCode.encode message.streamRejectCode

def decode (bytes : List UInt8) : Option (StreamRejectedMessage × List UInt8) := do
  let (streamRejectCode, bytes) ← StreamRejectCode.decode bytes
  pure ({ streamRejectCode }, bytes)

@[simp] theorem encode_length (message : StreamRejectedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [StreamRejectCode.encode_length]

theorem encode_length_pos (message : StreamRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [StreamRejectCode.decode_encode, some_bind]
  rfl

end StreamRejectedMessage

/-- Stream Complete Message: 8 bytes -/
structure StreamCompleteMessage where
  totalSequenceCount : BitVec 64
  deriving DecidableEq, Repr

namespace StreamCompleteMessage

def encode (message : StreamCompleteMessage) : List UInt8 :=
  encodeUInt 8 message.totalSequenceCount

def decode (bytes : List UInt8) : Option (StreamCompleteMessage × List UInt8) := do
  let (totalSequenceCount, bytes) ← decodeUInt 8 bytes
  pure ({ totalSequenceCount }, bytes)

@[simp] theorem encode_length (message : StreamCompleteMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : StreamCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StreamCompleteMessage

/-- Sequenced Message -/
structure SequencedMessage where
  sbeMessage : SbeMessage
  deriving DecidableEq, Repr

namespace SequencedMessage

def encode (message : SequencedMessage) : List UInt8 :=
  SbeMessage.encode message.sbeMessage

def decode (bytes : List UInt8) : Option (SequencedMessage × List UInt8) := do
  let (sbeMessage, bytes) ← SbeMessage.decode bytes
  pure ({ sbeMessage }, bytes)

theorem encode_length_pos (message : SequencedMessage) : (encode message).length > 0 := by
  have positive := SbeMessage.encode_length_pos message.sbeMessage
  unfold encode
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 65541 := by
  have bound_sbeMessage := SbeMessage.encode_length_le message.sbeMessage
  unfold encode
  omega

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SbeMessage.decode_encode, some_bind]
  rfl

end SequencedMessage

/-- Any Data, selected by Message Type -/
inductive Data where
  | loginRequestMessage (message : LoginRequestMessage) -- 100
  | replayRequestMessage (message : ReplayRequestMessage) -- 101
  | replayAllRequestMessage (message : ReplayAllRequestMessage) -- 102
  | streamRequestMessage (message : StreamRequestMessage) -- 103
  | unsequencedMessage (message : UnsequencedMessage) -- 104
  | loginAcceptedMessage (message : LoginAcceptedMessage) -- 1
  | loginRejectedMessage (message : LoginRejectedMessage) -- 2
  | startOfSessionMessage (message : StartOfSessionMessage) -- 3
  | replayBeginMessage (message : ReplayBeginMessage) -- 5
  | replayRejectedMessage (message : ReplayRejectedMessage) -- 6
  | replayCompleteMessage (message : ReplayCompleteMessage) -- 7
  | streamBeginMessage (message : StreamBeginMessage) -- 8
  | streamRejectedMessage (message : StreamRejectedMessage) -- 9
  | streamCompleteMessage (message : StreamCompleteMessage) -- 10
  | sequencedMessage (message : SequencedMessage) -- 11
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .loginRequestMessage _ => 100
  | .replayRequestMessage _ => 101
  | .replayAllRequestMessage _ => 102
  | .streamRequestMessage _ => 103
  | .unsequencedMessage _ => 104
  | .loginAcceptedMessage _ => 1
  | .loginRejectedMessage _ => 2
  | .startOfSessionMessage _ => 3
  | .replayBeginMessage _ => 5
  | .replayRejectedMessage _ => 6
  | .replayCompleteMessage _ => 7
  | .streamBeginMessage _ => 8
  | .streamRejectedMessage _ => 9
  | .streamCompleteMessage _ => 10
  | .sequencedMessage _ => 11

def encode : Data → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .replayAllRequestMessage message => ReplayAllRequestMessage.encode message
  | .streamRequestMessage message => StreamRequestMessage.encode message
  | .unsequencedMessage message => UnsequencedMessage.encode message
  | .loginAcceptedMessage message => LoginAcceptedMessage.encode message
  | .loginRejectedMessage message => LoginRejectedMessage.encode message
  | .startOfSessionMessage message => StartOfSessionMessage.encode message
  | .replayBeginMessage message => ReplayBeginMessage.encode message
  | .replayRejectedMessage message => ReplayRejectedMessage.encode message
  | .replayCompleteMessage message => ReplayCompleteMessage.encode message
  | .streamBeginMessage message => StreamBeginMessage.encode message
  | .streamRejectedMessage message => StreamRejectedMessage.encode message
  | .streamCompleteMessage message => StreamCompleteMessage.encode message
  | .sequencedMessage message => SequencedMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Data) : (encode message).length ≤ 65541 := by
  cases message with
  | loginRequestMessage inner =>
    simp only [encode, LoginRequestMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [encode, ReplayRequestMessage.encode_length]
    omega
  | replayAllRequestMessage inner =>
    simp only [encode, ReplayAllRequestMessage.encode_length]
    omega
  | streamRequestMessage inner =>
    simp only [encode, StreamRequestMessage.encode_length]
    omega
  | unsequencedMessage inner =>
    have bound_inner := UnsequencedMessage.encode_length_le inner
    simp only [encode]
    omega
  | loginAcceptedMessage inner =>
    simp only [encode, LoginAcceptedMessage.encode_length]
    omega
  | loginRejectedMessage inner =>
    simp only [encode, LoginRejectedMessage.encode_length]
    omega
  | startOfSessionMessage inner =>
    simp only [encode, StartOfSessionMessage.encode_length]
    omega
  | replayBeginMessage inner =>
    simp only [encode, ReplayBeginMessage.encode_length]
    omega
  | replayRejectedMessage inner =>
    simp only [encode, ReplayRejectedMessage.encode_length]
    omega
  | replayCompleteMessage inner =>
    simp only [encode, ReplayCompleteMessage.encode_length]
    omega
  | streamBeginMessage inner =>
    simp only [encode, StreamBeginMessage.encode_length]
    omega
  | streamRejectedMessage inner =>
    simp only [encode, StreamRejectedMessage.encode_length]
    omega
  | streamCompleteMessage inner =>
    simp only [encode, StreamCompleteMessage.encode_length]
    omega
  | sequencedMessage inner =>
    have bound_inner := SequencedMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Data × List UInt8) :=
  if tag = 100 then (LoginRequestMessage.decode bytes).map fun (message, rest) => (.loginRequestMessage message, rest)
  else if tag = 101 then (ReplayRequestMessage.decode bytes).map fun (message, rest) => (.replayRequestMessage message, rest)
  else if tag = 102 then (ReplayAllRequestMessage.decode bytes).map fun (message, rest) => (.replayAllRequestMessage message, rest)
  else if tag = 103 then (StreamRequestMessage.decode bytes).map fun (message, rest) => (.streamRequestMessage message, rest)
  else if tag = 104 then (UnsequencedMessage.decode bytes).map fun (message, rest) => (.unsequencedMessage message, rest)
  else if tag = 1 then (LoginAcceptedMessage.decode bytes).map fun (message, rest) => (.loginAcceptedMessage message, rest)
  else if tag = 2 then (LoginRejectedMessage.decode bytes).map fun (message, rest) => (.loginRejectedMessage message, rest)
  else if tag = 3 then (StartOfSessionMessage.decode bytes).map fun (message, rest) => (.startOfSessionMessage message, rest)
  else if tag = 5 then (ReplayBeginMessage.decode bytes).map fun (message, rest) => (.replayBeginMessage message, rest)
  else if tag = 6 then (ReplayRejectedMessage.decode bytes).map fun (message, rest) => (.replayRejectedMessage message, rest)
  else if tag = 7 then (ReplayCompleteMessage.decode bytes).map fun (message, rest) => (.replayCompleteMessage message, rest)
  else if tag = 8 then (StreamBeginMessage.decode bytes).map fun (message, rest) => (.streamBeginMessage message, rest)
  else if tag = 9 then (StreamRejectedMessage.decode bytes).map fun (message, rest) => (.streamRejectedMessage message, rest)
  else if tag = 10 then (StreamCompleteMessage.decode bytes).map fun (message, rest) => (.streamCompleteMessage message, rest)
  else if tag = 11 then (SequencedMessage.decode bytes).map fun (message, rest) => (.sequencedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Data) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Data

/-- Packet -/
structure Packet where
  messageLength : BitVec 16
  data : Data
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 (Data.tag message.data)
    ++ (encodeUInt 2 message.messageLength
    ++ (Data.encode message.data))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (data, bytes) ← Data.decode messageType bytes
  pure ({ messageLength, data }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 65544 := by
  unfold encode
  cases message.data with
  | loginRequestMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LoginRequestMessage.encode_length]
    omega
  | replayRequestMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ReplayRequestMessage.encode_length]
    omega
  | replayAllRequestMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ReplayAllRequestMessage.encode_length]
    omega
  | streamRequestMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StreamRequestMessage.encode_length]
    omega
  | unsequencedMessage inner =>
    have bound_inner := UnsequencedMessage.encode_length_le inner
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | loginAcceptedMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LoginAcceptedMessage.encode_length]
    omega
  | loginRejectedMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LoginRejectedMessage.encode_length]
    omega
  | startOfSessionMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StartOfSessionMessage.encode_length]
    omega
  | replayBeginMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ReplayBeginMessage.encode_length]
    omega
  | replayRejectedMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ReplayRejectedMessage.encode_length]
    omega
  | replayCompleteMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ReplayCompleteMessage.encode_length]
    omega
  | streamBeginMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StreamBeginMessage.encode_length]
    omega
  | streamRejectedMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StreamRejectedMessage.encode_length]
    omega
  | streamCompleteMessage inner =>
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, StreamCompleteMessage.encode_length]
    omega
  | sequencedMessage inner =>
    have bound_inner := SequencedMessage.encode_length_le inner
    simp only [Data.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Data.decode_encode, some_bind]
  rfl

end Packet

end Omi.LtseCommonheaderTcpV12
