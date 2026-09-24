import Omi.Wire

/-!
# Miami International Holdings MIAX Product Feed v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Application Message is not framed: its length Packet Length is not an integer it reads.

Note: Udp Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxMiaxoptionsMpfMachV11Udp

/-- Symbol Status: one byte code -/
def SymbolStatus.codes : List UInt8 :=
  [0x41, 0x49]

inductive SymbolStatus where
  | activeFuture -- Active Future
  | inactiveFuture -- Inactive Future
  | unlisted (byte : { byte : UInt8 // byte ∉ SymbolStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SymbolStatus

def toByte : SymbolStatus → UInt8
  | .activeFuture => 0x41
  | .inactiveFuture => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SymbolStatus :=
  if byte = 0x41 then .activeFuture
  else .inactiveFuture

def ofByte (byte : UInt8) : SymbolStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SymbolStatus) : ofByte value.toByte = value := by
  cases value with
  | activeFuture => decide
  | inactiveFuture => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SymbolStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SymbolStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SymbolStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SymbolStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SymbolStatus

/-- Heartbeat: 0 bytes -/
structure Heartbeat where
  deriving DecidableEq, Repr

namespace Heartbeat

def encode (_ : Heartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (Heartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : Heartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : Heartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end Heartbeat

/-- Start Of Session: 0 bytes -/
structure StartOfSession where
  deriving DecidableEq, Repr

namespace StartOfSession

def encode (_ : StartOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (StartOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : StartOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : StartOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end StartOfSession

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end EndOfSession

/-- System Time Message: 4 bytes -/
structure SystemTimeMessage where
  seconds : BitVec 32
  deriving DecidableEq, Repr

namespace SystemTimeMessage

def encode (message : SystemTimeMessage) : List UInt8 :=
  encodeUIntLE 4 message.seconds

def decode (bytes : List UInt8) : Option (SystemTimeMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds }, bytes)

@[simp] theorem encode_length (message : SystemTimeMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SystemTimeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemTimeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SystemTimeMessage

/-- Symbol Definition Message: 37 bytes -/
structure SymbolDefinitionMessage where
  nanoseconds : BitVec 32
  syntheticFutureSymbol : Alpha 8
  settlementDate : Alpha 8
  symbolStatus : SymbolStatus
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace SymbolDefinitionMessage

def encode (message : SymbolDefinitionMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.syntheticFutureSymbol
    ++ (Alpha.encode message.settlementDate
    ++ (SymbolStatus.encode message.symbolStatus
    ++ (Alpha.encode message.reserved16))))

def decode (bytes : List UInt8) : Option (SymbolDefinitionMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (syntheticFutureSymbol, bytes) ← Alpha.decode 8 bytes
  let (settlementDate, bytes) ← Alpha.decode 8 bytes
  let (symbolStatus, bytes) ← SymbolStatus.decode bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ nanoseconds, syntheticFutureSymbol, settlementDate, symbolStatus, reserved16 }, bytes)

@[simp] theorem encode_length (message : SymbolDefinitionMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SymbolStatus.encode_length]

theorem encode_length_pos (message : SymbolDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolStatus.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolDefinitionMessage

/-- Index Value Message: 13 bytes -/
structure IndexValueMessage where
  nanoseconds : BitVec 32
  symbol : Alpha 5
  value : BitVec 32
  deriving DecidableEq, Repr

namespace IndexValueMessage

def encode (message : IndexValueMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.value))

def decode (bytes : List UInt8) : Option (IndexValueMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 5 bytes
  let (value, bytes) ← decodeUIntLE 4 bytes
  pure ({ nanoseconds, symbol, value }, bytes)

@[simp] theorem encode_length (message : IndexValueMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : IndexValueMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndexValueMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IndexValueMessage

/-- Synthetic Future Value Message: 24 bytes -/
structure SyntheticFutureValueMessage where
  nanoseconds : BitVec 32
  syntheticFutureSymbol : Alpha 8
  value : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace SyntheticFutureValueMessage

def encode (message : SyntheticFutureValueMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.syntheticFutureSymbol
    ++ (encodeUIntLE 4 message.value
    ++ (Alpha.encode message.reserved8)))

def decode (bytes : List UInt8) : Option (SyntheticFutureValueMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (syntheticFutureSymbol, bytes) ← Alpha.decode 8 bytes
  let (value, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ nanoseconds, syntheticFutureSymbol, value, reserved8 }, bytes)

@[simp] theorem encode_length (message : SyntheticFutureValueMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SyntheticFutureValueMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SyntheticFutureValueMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SyntheticFutureValueMessage

/-- Any Data, selected by Message Type -/
inductive Data where
  | systemTimeMessage (message : SystemTimeMessage) -- "1" 0x31
  | symbolDefinitionMessage (message : SymbolDefinitionMessage) -- "s" 0x73
  | indexValueMessage (message : IndexValueMessage) -- "I" 0x49
  | syntheticFutureValueMessage (message : SyntheticFutureValueMessage) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .systemTimeMessage _ => 49
  | .symbolDefinitionMessage _ => 115
  | .indexValueMessage _ => 73
  | .syntheticFutureValueMessage _ => 90

def encode : Data → List UInt8
  | .systemTimeMessage message => SystemTimeMessage.encode message
  | .symbolDefinitionMessage message => SymbolDefinitionMessage.encode message
  | .indexValueMessage message => IndexValueMessage.encode message
  | .syntheticFutureValueMessage message => SyntheticFutureValueMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Data) : (encode message).length ≤ 37 := by
  cases message with
  | systemTimeMessage inner =>
    simp only [encode, SystemTimeMessage.encode_length]
    omega
  | symbolDefinitionMessage inner =>
    simp only [encode, SymbolDefinitionMessage.encode_length]
    omega
  | indexValueMessage inner =>
    simp only [encode, IndexValueMessage.encode_length]
    omega
  | syntheticFutureValueMessage inner =>
    simp only [encode, SyntheticFutureValueMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Data × List UInt8) :=
  if tag = 49 then (SystemTimeMessage.decode bytes).map fun (message, rest) => (.systemTimeMessage message, rest)
  else if tag = 115 then (SymbolDefinitionMessage.decode bytes).map fun (message, rest) => (.symbolDefinitionMessage message, rest)
  else if tag = 73 then (IndexValueMessage.decode bytes).map fun (message, rest) => (.indexValueMessage message, rest)
  else if tag = 90 then (SyntheticFutureValueMessage.decode bytes).map fun (message, rest) => (.syntheticFutureValueMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Data) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Data

/-- Application Message -/
structure ApplicationMessage where
  data : Data
  deriving DecidableEq, Repr

namespace ApplicationMessage

def encode (message : ApplicationMessage) : List UInt8 :=
  encodeUInt 1 (Data.tag message.data)
    ++ (Data.encode message.data)

def decode (bytes : List UInt8) : Option (ApplicationMessage × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (data, bytes) ← Data.decode messageType bytes
  pure ({ data }, bytes)

theorem encode_length_pos (message : ApplicationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ApplicationMessage) : (encode message).length ≤ 38 := by
  unfold encode
  cases message.data with
  | systemTimeMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SystemTimeMessage.encode_length]
    omega
  | symbolDefinitionMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SymbolDefinitionMessage.encode_length]
    omega
  | indexValueMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, IndexValueMessage.encode_length]
    omega
  | syntheticFutureValueMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SyntheticFutureValueMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ApplicationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Data.decode_encode, some_bind]
  rfl

end ApplicationMessage

/-- Any Payload, selected by Packet Type -/
inductive Payload where
  | heartbeat (message : Heartbeat) -- 0
  | startOfSession (message : StartOfSession) -- 1
  | endOfSession (message : EndOfSession) -- 2
  | applicationMessage (message : ApplicationMessage) -- 3
  deriving DecidableEq, Repr

namespace Payload

/-- The Packet Type each message is sent under -/
def tag : Payload → BitVec 8
  | .heartbeat _ => 0
  | .startOfSession _ => 1
  | .endOfSession _ => 2
  | .applicationMessage _ => 3

def encode : Payload → List UInt8
  | .heartbeat message => Heartbeat.encode message
  | .startOfSession message => StartOfSession.encode message
  | .endOfSession message => EndOfSession.encode message
  | .applicationMessage message => ApplicationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 38 := by
  cases message with
  | heartbeat inner =>
    simp only [encode, Heartbeat.encode_length]
    omega
  | startOfSession inner =>
    simp only [encode, StartOfSession.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 0 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 1 then (StartOfSession.decode bytes).map fun (message, rest) => (.startOfSession message, rest)
  else if tag = 2 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
  else if tag = 3 then (ApplicationMessage.decode bytes).map fun (message, rest) => (.applicationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Mach Message -/
structure MachMessage where
  sequenceNumber : BitVec 64
  packetLength : BitVec 16
  sessionNumber : BitVec 8
  payload : Payload
  deriving DecidableEq, Repr

namespace MachMessage

def encode (message : MachMessage) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUIntLE 2 message.packetLength
    ++ (encodeUIntLE 1 (Payload.tag message.payload)
    ++ (encodeUIntLE 1 message.sessionNumber
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (MachMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (packetLength, bytes) ← decodeUIntLE 2 bytes
  let (packetType, bytes) ← decodeUIntLE 1 bytes
  let (sessionNumber, bytes) ← decodeUIntLE 1 bytes
  let (payload, bytes) ← Payload.decode packetType bytes
  pure ({ sequenceNumber, packetLength, sessionNumber, payload }, bytes)

theorem encode_length_pos (message : MachMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MachMessage) : (encode message).length ≤ 50 := by
  unfold encode
  cases message.payload with
  | heartbeat inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Heartbeat.encode_length]
    omega
  | startOfSession inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, StartOfSession.encode_length]
    omega
  | endOfSession inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EndOfSession.encode_length]
    omega
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega

@[simp] theorem decode_encode (message : MachMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end MachMessage

/-- Udp Packet -/
structure UdpPacket where
  machMessage : List MachMessage
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  encodeMany MachMessage.encode message.machMessage

def decode (bytes : List UInt8) : Option UdpPacket := do
  let machMessage ← decodeAll MachMessage.decode bytes.length bytes
  pure { machMessage }

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany MachMessage.encode MachMessage.decode MachMessage.decode_encode MachMessage.encode_length_pos message.machMessage _ (encodeMany_length_ge MachMessage.encode MachMessage.encode_length_pos message.machMessage), some_bind]
  rfl

end UdpPacket

end Omi.MiaxMiaxoptionsMpfMachV11Udp
