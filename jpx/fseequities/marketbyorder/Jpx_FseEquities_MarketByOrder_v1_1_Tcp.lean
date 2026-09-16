import Omi.Wire

/-!
# Japan Exchange Group Market By Order v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.JpxFseequitiesMarketbyorderFlexV11Tcp

/-- Result Code: one byte code -/
inductive ResultCode where
  | accepted -- Accepted
  | outOfService -- Out Of Service
  | incorrectUserId -- Incorrect User Id
  | incorrectSequenceNumber -- Incorrect Sequence Number
  | incorrectPacketType -- Incorrect Packet Type
  | incorrectMcgNumber -- Incorrect Mcg Number
  | otherError -- Other Error
  deriving DecidableEq, Repr

namespace ResultCode

def toByte : ResultCode → UInt8
  | .accepted => 0x41
  | .outOfService => 0x4F
  | .incorrectUserId => 0x55
  | .incorrectSequenceNumber => 0x53
  | .incorrectPacketType => 0x54
  | .incorrectMcgNumber => 0x4D
  | .otherError => 0x5A

def ofByte? (byte : UInt8) : Option ResultCode :=
  if byte = 0x41 then some .accepted
  else if byte = 0x4F then some .outOfService
  else if byte = 0x55 then some .incorrectUserId
  else if byte = 0x53 then some .incorrectSequenceNumber
  else if byte = 0x54 then some .incorrectPacketType
  else if byte = 0x4D then some .incorrectMcgNumber
  else if byte = 0x5A then some .otherError
  else none

theorem ofByte?_toByte (value : ResultCode) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : ResultCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ResultCode × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : ResultCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ResultCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end ResultCode

/-- Login Request Message: 15 bytes -/
structure LoginRequestMessage where
  userId : Alpha 6
  multicastGroupNumber : BitVec 8
  numberOfSystemReboots : BitVec 8
  sequenceNumber : BitVec 32
  requestedMessageCount : BitVec 24
  deriving DecidableEq, Repr

namespace LoginRequestMessage

def encode (message : LoginRequestMessage) : List UInt8 :=
  Alpha.encode message.userId
    ++ encodeUInt 1 message.multicastGroupNumber
    ++ encodeUInt 1 message.numberOfSystemReboots
    ++ encodeUInt 4 message.sequenceNumber
    ++ encodeUInt 3 message.requestedMessageCount

def decode (bytes : List UInt8) : Option (LoginRequestMessage × List UInt8) := do
  let (userId, bytes) ← Alpha.decode 6 bytes
  let (multicastGroupNumber, bytes) ← decodeUInt 1 bytes
  let (numberOfSystemReboots, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← decodeUInt 4 bytes
  let (requestedMessageCount, bytes) ← decodeUInt 3 bytes
  pure ({ userId, multicastGroupNumber, numberOfSystemReboots, sequenceNumber, requestedMessageCount }, bytes)

@[simp] theorem encode_length (message : LoginRequestMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LoginRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequestMessage) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end LoginRequestMessage

/-- Login Result Message: 2 bytes -/
structure LoginResultMessage where
  multicastGroupNumber : BitVec 8
  resultCode : ResultCode
  deriving DecidableEq, Repr

namespace LoginResultMessage

def encode (message : LoginResultMessage) : List UInt8 :=
  encodeUInt 1 message.multicastGroupNumber
    ++ ResultCode.encode message.resultCode

def decode (bytes : List UInt8) : Option (LoginResultMessage × List UInt8) := do
  let (multicastGroupNumber, bytes) ← decodeUInt 1 bytes
  let (resultCode, bytes) ← ResultCode.decode bytes
  pure ({ multicastGroupNumber, resultCode }, bytes)

@[simp] theorem encode_length (message : LoginResultMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ResultCode.encode_length]

theorem encode_length_pos (message : LoginResultMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResultMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [ResultCode.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginResultMessage) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end LoginResultMessage

/-- Message Response Message -/
structure MessageResponseMessage where
  data : Capped 65517
  deriving DecidableEq, Repr

namespace MessageResponseMessage

def encode (message : MessageResponseMessage) : List UInt8 :=
  message.data.val

def decode (bytes : List UInt8) : Option MessageResponseMessage := do
  let data_ := bytes
  if fits_data : data_.length ≤ 65517 then
    pure { data := ⟨data_, fits_data⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MessageResponseMessage) : (encode message).length ≤ 65517 := by
  have bound_data := message.data.length_le
  unfold encode
  omega

theorem decode_encode (message : MessageResponseMessage) : decode (encode message) = some message := by
  unfold decode encode
  simp only [message.data.length_le, ↓reduceDIte]
  rfl

end MessageResponseMessage

/-- End Of Message Message: 6 bytes -/
structure EndOfMessageMessage where
  multicastGroupNumber : BitVec 8
  numberOfSystemReboots : BitVec 8
  nextSequenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace EndOfMessageMessage

def encode (message : EndOfMessageMessage) : List UInt8 :=
  encodeUInt 1 message.multicastGroupNumber
    ++ encodeUInt 1 message.numberOfSystemReboots
    ++ encodeUInt 4 message.nextSequenceNumber

def decode (bytes : List UInt8) : Option (EndOfMessageMessage × List UInt8) := do
  let (multicastGroupNumber, bytes) ← decodeUInt 1 bytes
  let (numberOfSystemReboots, bytes) ← decodeUInt 1 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 4 bytes
  pure ({ multicastGroupNumber, numberOfSystemReboots, nextSequenceNumber }, bytes)

@[simp] theorem encode_length (message : EndOfMessageMessage) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : EndOfMessageMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfMessageMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfMessageMessage) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end EndOfMessageMessage

/-- Any Tcp Payload, selected by Packet Type -/
inductive TcpPayload where
  | loginRequestMessage (message : LoginRequestMessage) -- 'R' 0x52
  | loginResultMessage (message : LoginResultMessage) -- 'A' 0x41
  | messageResponseMessage (message : MessageResponseMessage) -- 'S' 0x53
  | endOfMessageMessage (message : EndOfMessageMessage) -- 'G' 0x47
  deriving DecidableEq, Repr

namespace TcpPayload

/-- The Packet Type each message is sent under -/
def tag : TcpPayload → BitVec 8
  | .loginRequestMessage _ => 82
  | .loginResultMessage _ => 65
  | .messageResponseMessage _ => 83
  | .endOfMessageMessage _ => 71

def encode : TcpPayload → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .loginResultMessage message => LoginResultMessage.encode message
  | .messageResponseMessage message => MessageResponseMessage.encode message
  | .endOfMessageMessage message => EndOfMessageMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option TcpPayload :=
  if tag = 82 then (LoginRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequestMessage message) else none
  else if tag = 65 then (LoginResultMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginResultMessage message) else none
  else if tag = 83 then (MessageResponseMessage.decode bytes).map fun message => .messageResponseMessage message
  else if tag = 71 then (EndOfMessageMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfMessageMessage message) else none
  else none

theorem decode_encode (message : TcpPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | loginRequestMessage message => simp [decode, encode, tag, LoginRequestMessage.decode_encode_nil]
  | loginResultMessage message => simp [decode, encode, tag, LoginResultMessage.decode_encode_nil]
  | messageResponseMessage message => simp [decode, encode, tag, MessageResponseMessage.decode_encode]
  | endOfMessageMessage message => simp [decode, encode, tag, EndOfMessageMessage.decode_encode_nil]

end TcpPayload

/-- Tcp Packet -/
structure TcpPacket where
  tcpPayload : TcpPayload
  deriving DecidableEq, Repr

namespace TcpPacket

def encodeBody (message : TcpPacket) : List UInt8 :=
  encodeUInt 1 (TcpPayload.tag message.tcpPayload)
    ++ TcpPayload.encode message.tcpPayload

def decodeBody (bytes : List UInt8) : Option TcpPacket := do
  let (packetType, bytes) ← decodeUInt 1 bytes
  let tcpPayload ← TcpPayload.decode packetType bytes
  pure { tcpPayload }

theorem decodeBody_encodeBody (message : TcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  simp only [Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [TcpPayload.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : TcpPacket) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.tcpPayload with
  | loginRequestMessage inner =>
    simp only [TcpPayload.encode, List.length_append, encodeUInt_length, LoginRequestMessage.encode_length]
    omega
  | loginResultMessage inner =>
    simp only [TcpPayload.encode, List.length_append, encodeUInt_length, LoginResultMessage.encode_length]
    omega
  | messageResponseMessage inner =>
    have bound_inner := MessageResponseMessage.encode_length_le inner
    simp only [TcpPayload.encode, List.length_append, encodeUInt_length]
    omega
  | endOfMessageMessage inner =>
    simp only [TcpPayload.encode, List.length_append, encodeUInt_length, EndOfMessageMessage.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : TcpPacket → List UInt8 :=
  encodeFramed 2 2 encodeBody

def decode : List UInt8 → Option (TcpPacket × List UInt8) :=
  decodeFramedAll 2 2 decodeBody

@[simp] theorem decode_encode (message : TcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAll_encodeFramed 2 2 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : TcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end TcpPacket

end Omi.JpxFseequitiesMarketbyorderFlexV11Tcp
