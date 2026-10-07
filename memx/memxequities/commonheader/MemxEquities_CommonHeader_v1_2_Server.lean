import Wire

/-!
# The Members Exchange Common Header v1.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Message is not framed: its length Message Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MemxMemxequitiesCommonheaderTcpV12Server

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginAcceptedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRejectedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : StartOfSessionMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ReplayBeginMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ReplayRejectedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ReplayCompleteMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : StreamBeginMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : StreamRejectedMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : StreamCompleteMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end StreamCompleteMessage

/-- Sequenced Message -/
structure SequencedMessage where
  sbeMessage : List UInt8
  deriving DecidableEq, Repr

namespace SequencedMessage

def encode (message : SequencedMessage) : List UInt8 :=
  encodeMany Byte.encode message.sbeMessage

def decode (bytes : List UInt8) : Option SequencedMessage := do
  let sbeMessage ← decodeAll Byte.decode bytes.length bytes
  pure { sbeMessage }

theorem decode_encode (message : SequencedMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Byte.encode Byte.decode Byte.decode_encode Byte.encode_length_pos message.sbeMessage _ (encodeMany_length_ge Byte.encode Byte.encode_length_pos message.sbeMessage), some_bind]
  rfl

end SequencedMessage

/-- Any Server Data, selected by Message Type -/
inductive ServerData where
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

namespace ServerData

/-- The Message Type each message is sent under -/
def tag : ServerData → BitVec 8
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

def encode : ServerData → List UInt8
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

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ServerData :=
  if tag = 1 then (LoginAcceptedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginAcceptedMessage message) else none
  else if tag = 2 then (LoginRejectedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRejectedMessage message) else none
  else if tag = 3 then (StartOfSessionMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.startOfSessionMessage message) else none
  else if tag = 5 then (ReplayBeginMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.replayBeginMessage message) else none
  else if tag = 6 then (ReplayRejectedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.replayRejectedMessage message) else none
  else if tag = 7 then (ReplayCompleteMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.replayCompleteMessage message) else none
  else if tag = 8 then (StreamBeginMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.streamBeginMessage message) else none
  else if tag = 9 then (StreamRejectedMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.streamRejectedMessage message) else none
  else if tag = 10 then (StreamCompleteMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.streamCompleteMessage message) else none
  else if tag = 11 then (SequencedMessage.decode bytes).map fun message => .sequencedMessage message
  else none

theorem decode_encode (message : ServerData) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | loginAcceptedMessage message => simp [decode, encode, tag, LoginAcceptedMessage.decode_encode_nil]
  | loginRejectedMessage message => simp [decode, encode, tag, LoginRejectedMessage.decode_encode_nil]
  | startOfSessionMessage message => simp [decode, encode, tag, StartOfSessionMessage.decode_encode_nil]
  | replayBeginMessage message => simp [decode, encode, tag, ReplayBeginMessage.decode_encode_nil]
  | replayRejectedMessage message => simp [decode, encode, tag, ReplayRejectedMessage.decode_encode_nil]
  | replayCompleteMessage message => simp [decode, encode, tag, ReplayCompleteMessage.decode_encode_nil]
  | streamBeginMessage message => simp [decode, encode, tag, StreamBeginMessage.decode_encode_nil]
  | streamRejectedMessage message => simp [decode, encode, tag, StreamRejectedMessage.decode_encode_nil]
  | streamCompleteMessage message => simp [decode, encode, tag, StreamCompleteMessage.decode_encode_nil]
  | sequencedMessage message => simp [decode, encode, tag, SequencedMessage.decode_encode]

end ServerData

/-- Server Packet -/
structure ServerPacket where
  messageLength : BitVec 16
  serverData : ServerData
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeUInt 1 (ServerData.tag message.serverData)
    ++ (encodeUInt 2 message.messageLength
    ++ (ServerData.encode message.serverData))

def decode (bytes : List UInt8) : Option ServerPacket := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let serverData ← ServerData.decode messageType bytes
  pure { messageLength, serverData }

theorem encode_length_pos (message : ServerPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerData.decode_encode, some_bind]
  rfl

end ServerPacket

end Omi.MemxMemxequitiesCommonheaderTcpV12Server
