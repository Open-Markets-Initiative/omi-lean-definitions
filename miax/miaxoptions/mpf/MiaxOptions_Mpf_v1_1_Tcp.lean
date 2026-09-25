import Omi.Wire

/-!
# Miami International Holdings MIAX Product Feed v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Sesm Packet Length is not an integer it reads.

Note: Application Message is not framed: its length Sesm Packet Length is not an integer it reads.

Note: Unsequenced Data Packet is not framed: its length Sesm Packet Length is not an integer it reads.

Note: Sesm Tcp Packet's body has no bound its 2 byte Sesm Packet Length must fit, so every message carries the proof its own encoding fits: the record is its body with that proof, checked as the frame is read.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxMiaxoptionsMpfMachV11Tcp

/-- Refresh Message Type: one byte code -/
def RefreshMessageType.codes : List UInt8 :=
  [0x49, 0x5A]

inductive RefreshMessageType where
  | indexUpdateRefresh -- Index Update Refresh
  | syntheticFutureValues -- Synthetic Future Values
  | unlisted (byte : { byte : UInt8 // byte ∉ RefreshMessageType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RefreshMessageType

def toByte : RefreshMessageType → UInt8
  | .indexUpdateRefresh => 0x49
  | .syntheticFutureValues => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RefreshMessageType :=
  if byte = 0x49 then .indexUpdateRefresh
  else .syntheticFutureValues

def ofByte (byte : UInt8) : RefreshMessageType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RefreshMessageType) : ofByte value.toByte = value := by
  cases value with
  | indexUpdateRefresh => decide
  | syntheticFutureValues => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RefreshMessageType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RefreshMessageType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RefreshMessageType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RefreshMessageType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RefreshMessageType

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

/-- Login Status: one byte code -/
def LoginStatus.codes : List UInt8 :=
  [0x20, 0x53, 0x55, 0x58, 0x4E, 0x49, 0x41, 0x4C]

inductive LoginStatus where
  | successful -- Successful
  | invalidTradingSessionRequested -- Invalid Trading Session Requested
  | noActiveTradingSessionExists -- No Active Trading Session Exists
  | rejected -- Rejected
  | invalidStartSequenceNumberRequested -- Invalid Start Sequence Number Requested
  | incompatibleSessionProtocolVersion -- Incompatible Session Protocol Version
  | incompatibleApplicationProtocolVersion -- Incompatible Application Protocol Version
  | requestRejectedBecauseClientAlreadyLoggedIn -- Request Rejected Because Client Already Logged In
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginStatus

def toByte : LoginStatus → UInt8
  | .successful => 0x20
  | .invalidTradingSessionRequested => 0x53
  | .noActiveTradingSessionExists => 0x55
  | .rejected => 0x58
  | .invalidStartSequenceNumberRequested => 0x4E
  | .incompatibleSessionProtocolVersion => 0x49
  | .incompatibleApplicationProtocolVersion => 0x41
  | .requestRejectedBecauseClientAlreadyLoggedIn => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x53 then .invalidTradingSessionRequested
  else if byte = 0x55 then .noActiveTradingSessionExists
  else if byte = 0x58 then .rejected
  else if byte = 0x4E then .invalidStartSequenceNumberRequested
  else if byte = 0x49 then .incompatibleSessionProtocolVersion
  else if byte = 0x41 then .incompatibleApplicationProtocolVersion
  else .requestRejectedBecauseClientAlreadyLoggedIn

def ofByte (byte : UInt8) : LoginStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | invalidTradingSessionRequested => decide
  | noActiveTradingSessionExists => decide
  | rejected => decide
  | invalidStartSequenceNumberRequested => decide
  | incompatibleSessionProtocolVersion => decide
  | incompatibleApplicationProtocolVersion => decide
  | requestRejectedBecauseClientAlreadyLoggedIn => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LoginStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LoginStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LoginStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LoginStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LoginStatus

/-- Logout Reason: one byte code -/
def LogoutReason.codes : List UInt8 :=
  [0x20, 0x42, 0x4C, 0x41]

inductive LogoutReason where
  | gracefulLogout -- Graceful Logout
  | badPacket -- Bad Packet
  | timedOut -- Timed Out
  | applicationTerminatingConnection -- Application Terminating Connection
  | unlisted (byte : { byte : UInt8 // byte ∉ LogoutReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LogoutReason

def toByte : LogoutReason → UInt8
  | .gracefulLogout => 0x20
  | .badPacket => 0x42
  | .timedOut => 0x4C
  | .applicationTerminatingConnection => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LogoutReason :=
  if byte = 0x20 then .gracefulLogout
  else if byte = 0x42 then .badPacket
  else if byte = 0x4C then .timedOut
  else .applicationTerminatingConnection

def ofByte (byte : UInt8) : LogoutReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LogoutReason) : ofByte value.toByte = value := by
  cases value with
  | gracefulLogout => decide
  | badPacket => decide
  | timedOut => decide
  | applicationTerminatingConnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LogoutReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LogoutReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LogoutReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LogoutReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LogoutReason

/-- Sequenced Data Packet: 10 bytes -/
structure SequencedDataPacket where
  sequenceNumber : BitVec 64
  matchingEngineId : BitVec 8
  sequencedMessageType : Alpha 1
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUInt 1 message.matchingEngineId
    ++ (Alpha.encode message.sequencedMessageType))

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (matchingEngineId, bytes) ← decodeUInt 1 bytes
  let (sequencedMessageType, bytes) ← Alpha.decode 1 bytes
  pure ({ sequenceNumber, matchingEngineId, sequencedMessageType }, bytes)

@[simp] theorem encode_length (message : SequencedDataPacket) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedDataPacket

/-- Refresh Request Message: 1 bytes -/
structure RefreshRequestMessage where
  refreshMessageType : RefreshMessageType
  deriving DecidableEq, Repr

namespace RefreshRequestMessage

def encode (message : RefreshRequestMessage) : List UInt8 :=
  RefreshMessageType.encode message.refreshMessageType

def decode (bytes : List UInt8) : Option (RefreshRequestMessage × List UInt8) := do
  let (refreshMessageType, bytes) ← RefreshMessageType.decode bytes
  pure ({ refreshMessageType }, bytes)

@[simp] theorem encode_length (message : RefreshRequestMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [RefreshMessageType.encode_length]

theorem encode_length_pos (message : RefreshRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RefreshMessageType.decode_encode, some_bind]
  rfl

end RefreshRequestMessage

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

/-- Refresh Response Message -/
structure RefreshResponseMessage where
  sequenceNumber : BitVec 64
  applicationMessage : ApplicationMessage
  deriving DecidableEq, Repr

namespace RefreshResponseMessage

def encode (message : RefreshResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (ApplicationMessage.encode message.applicationMessage)

def decode (bytes : List UInt8) : Option (RefreshResponseMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (applicationMessage, bytes) ← ApplicationMessage.decode bytes
  pure ({ sequenceNumber, applicationMessage }, bytes)

theorem encode_length_pos (message : RefreshResponseMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : RefreshResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ApplicationMessage.decode_encode, some_bind]
  rfl

end RefreshResponseMessage

/-- End Of Refresh Notification Message: 1 bytes -/
structure EndOfRefreshNotificationMessage where
  refreshMessageType : RefreshMessageType
  deriving DecidableEq, Repr

namespace EndOfRefreshNotificationMessage

def encode (message : EndOfRefreshNotificationMessage) : List UInt8 :=
  RefreshMessageType.encode message.refreshMessageType

def decode (bytes : List UInt8) : Option (EndOfRefreshNotificationMessage × List UInt8) := do
  let (refreshMessageType, bytes) ← RefreshMessageType.decode bytes
  pure ({ refreshMessageType }, bytes)

@[simp] theorem encode_length (message : EndOfRefreshNotificationMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [RefreshMessageType.encode_length]

theorem encode_length_pos (message : EndOfRefreshNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfRefreshNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RefreshMessageType.decode_encode, some_bind]
  rfl

end EndOfRefreshNotificationMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | refreshRequestMessage (message : RefreshRequestMessage) -- "R" 0x52
  | refreshResponseMessage (message : RefreshResponseMessage) -- "r" 0x72
  | endOfRefreshNotificationMessage (message : EndOfRefreshNotificationMessage) -- "E" 0x45
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .refreshRequestMessage _ => 82
  | .refreshResponseMessage _ => 114
  | .endOfRefreshNotificationMessage _ => 69

def encode : UnsequencedMessage → List UInt8
  | .refreshRequestMessage message => RefreshRequestMessage.encode message
  | .refreshResponseMessage message => RefreshResponseMessage.encode message
  | .endOfRefreshNotificationMessage message => EndOfRefreshNotificationMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 82 then (RefreshRequestMessage.decode bytes).map fun (message, rest) => (.refreshRequestMessage message, rest)
  else if tag = 114 then (RefreshResponseMessage.decode bytes).map fun (message, rest) => (.refreshResponseMessage message, rest)
  else if tag = 69 then (EndOfRefreshNotificationMessage.decode bytes).map fun (message, rest) => (.endOfRefreshNotificationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UnsequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UnsequencedDataPacket

/-- Login Request: 35 bytes -/
structure LoginRequest where
  sesmVersion : Alpha 5
  username : Alpha 5
  computerId : Alpha 8
  applicationProtocol : Alpha 8
  requestedTradingSessionId : BitVec 8
  requestedSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginRequest

def encode (message : LoginRequest) : List UInt8 :=
  Alpha.encode message.sesmVersion
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.computerId
    ++ (Alpha.encode message.applicationProtocol
    ++ (encodeUInt 1 message.requestedTradingSessionId
    ++ (encodeUIntLE 8 message.requestedSequenceNumber)))))

def decode (bytes : List UInt8) : Option (LoginRequest × List UInt8) := do
  let (sesmVersion, bytes) ← Alpha.decode 5 bytes
  let (username, bytes) ← Alpha.decode 5 bytes
  let (computerId, bytes) ← Alpha.decode 8 bytes
  let (applicationProtocol, bytes) ← Alpha.decode 8 bytes
  let (requestedTradingSessionId, bytes) ← decodeUInt 1 bytes
  let (requestedSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ sesmVersion, username, computerId, applicationProtocol, requestedTradingSessionId, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequest) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequest

/-- Login Response: 11 bytes -/
structure LoginResponse where
  numberOfMatchingEngines : BitVec 8
  loginStatus : LoginStatus
  tradingSessionId : BitVec 8
  highestSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginResponse

def encode (message : LoginResponse) : List UInt8 :=
  encodeUInt 1 message.numberOfMatchingEngines
    ++ (LoginStatus.encode message.loginStatus
    ++ (encodeUInt 1 message.tradingSessionId
    ++ (encodeUIntLE 8 message.highestSequenceNumber)))

def decode (bytes : List UInt8) : Option (LoginResponse × List UInt8) := do
  let (numberOfMatchingEngines, bytes) ← decodeUInt 1 bytes
  let (loginStatus, bytes) ← LoginStatus.decode bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (highestSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ numberOfMatchingEngines, loginStatus, tradingSessionId, highestSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginResponse) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LoginStatus.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LoginStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginResponse

/-- Synchronization Complete: 1 bytes -/
structure SynchronizationComplete where
  numberOfMatchingEngines : BitVec 8
  deriving DecidableEq, Repr

namespace SynchronizationComplete

def encode (message : SynchronizationComplete) : List UInt8 :=
  encodeUInt 1 message.numberOfMatchingEngines

def decode (bytes : List UInt8) : Option (SynchronizationComplete × List UInt8) := do
  let (numberOfMatchingEngines, bytes) ← decodeUInt 1 bytes
  pure ({ numberOfMatchingEngines }, bytes)

@[simp] theorem encode_length (message : SynchronizationComplete) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SynchronizationComplete) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SynchronizationComplete) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SynchronizationComplete) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SynchronizationComplete

/-- Retransmission Request: 16 bytes -/
structure RetransmissionRequest where
  startSequenceNumber : BitVec 64
  endSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace RetransmissionRequest

def encode (message : RetransmissionRequest) : List UInt8 :=
  encodeUIntLE 8 message.startSequenceNumber
    ++ (encodeUIntLE 8 message.endSequenceNumber)

def decode (bytes : List UInt8) : Option (RetransmissionRequest × List UInt8) := do
  let (startSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (endSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ startSequenceNumber, endSequenceNumber }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequest) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmissionRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmissionRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RetransmissionRequest

/-- Logout Request -/
structure LogoutRequest where
  logoutReason : LogoutReason
  logoutText : Capped 65487
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option LogoutRequest := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 65487 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogoutRequest) : (encode message).length ≤ 65488 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, LogoutReason.encode_length]
  omega

theorem decode_encode (message : LogoutRequest) : decode (encode message) = some message := by
  unfold decode encode
  rw [LogoutReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end LogoutRequest

/-- Goodbye Packet -/
structure GoodbyePacket where
  logoutReason : LogoutReason
  logoutText : Capped 65487
  deriving DecidableEq, Repr

namespace GoodbyePacket

def encode (message : GoodbyePacket) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option GoodbyePacket := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 65487 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : GoodbyePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GoodbyePacket) : (encode message).length ≤ 65488 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, LogoutReason.encode_length]
  omega

theorem decode_encode (message : GoodbyePacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [LogoutReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end GoodbyePacket

/-- Trading Session Update: 0 bytes -/
structure TradingSessionUpdate where
  deriving DecidableEq, Repr

namespace TradingSessionUpdate

def encode (_ : TradingSessionUpdate) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (TradingSessionUpdate × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : TradingSessionUpdate) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TradingSessionUpdate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradingSessionUpdate) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradingSessionUpdate

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServerHeartbeat

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClientHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ClientHeartbeat

/-- Test Packet -/
structure TestPacket where
  testText : Capped 65487
  deriving DecidableEq, Repr

namespace TestPacket

def encode (message : TestPacket) : List UInt8 :=
  message.testText.val

def decode (bytes : List UInt8) : Option TestPacket := do
  let testText_ := bytes
  if fits_testText : testText_.length ≤ 65487 then
    pure { testText := ⟨testText_, fits_testText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TestPacket) : (encode message).length ≤ 65487 := by
  have bound_testText := message.testText.length_le
  unfold encode
  omega

theorem decode_encode (message : TestPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.testText.length_le]
  rfl

end TestPacket

/-- Any Sesm Payload, selected by Sesm Packet Type -/
inductive SesmPayload where
  | sequencedDataPacket (message : SequencedDataPacket) -- "s" 0x73
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | loginRequest (message : LoginRequest) -- "l" 0x6C
  | loginResponse (message : LoginResponse) -- "r" 0x72
  | synchronizationComplete (message : SynchronizationComplete) -- "c" 0x63
  | retransmissionRequest (message : RetransmissionRequest) -- "a" 0x61
  | logoutRequest (message : LogoutRequest) -- "X" 0x58
  | goodbyePacket (message : GoodbyePacket) -- "G" 0x47
  | tradingSessionUpdate (message : TradingSessionUpdate) -- "u" 0x75
  | serverHeartbeat (message : ServerHeartbeat) -- "0" 0x30
  | clientHeartbeat (message : ClientHeartbeat) -- "1" 0x31
  | testPacket (message : TestPacket) -- "T" 0x54
  deriving DecidableEq, Repr

namespace SesmPayload

/-- The Sesm Packet Type each message is sent under -/
def tag : SesmPayload → BitVec 8
  | .sequencedDataPacket _ => 115
  | .unsequencedDataPacket _ => 85
  | .loginRequest _ => 108
  | .loginResponse _ => 114
  | .synchronizationComplete _ => 99
  | .retransmissionRequest _ => 97
  | .logoutRequest _ => 88
  | .goodbyePacket _ => 71
  | .tradingSessionUpdate _ => 117
  | .serverHeartbeat _ => 48
  | .clientHeartbeat _ => 49
  | .testPacket _ => 84

def encode : SesmPayload → List UInt8
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .loginRequest message => LoginRequest.encode message
  | .loginResponse message => LoginResponse.encode message
  | .synchronizationComplete message => SynchronizationComplete.encode message
  | .retransmissionRequest message => RetransmissionRequest.encode message
  | .logoutRequest message => LogoutRequest.encode message
  | .goodbyePacket message => GoodbyePacket.encode message
  | .tradingSessionUpdate message => TradingSessionUpdate.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message
  | .testPacket message => TestPacket.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option SesmPayload :=
  if tag = 115 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsequencedDataPacket message) else none
  else if tag = 108 then (LoginRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequest message) else none
  else if tag = 114 then (LoginResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginResponse message) else none
  else if tag = 99 then (SynchronizationComplete.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.synchronizationComplete message) else none
  else if tag = 97 then (RetransmissionRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmissionRequest message) else none
  else if tag = 88 then (LogoutRequest.decode bytes).map fun message => .logoutRequest message
  else if tag = 71 then (GoodbyePacket.decode bytes).map fun message => .goodbyePacket message
  else if tag = 117 then (TradingSessionUpdate.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradingSessionUpdate message) else none
  else if tag = 48 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 49 then (ClientHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clientHeartbeat message) else none
  else if tag = 84 then (TestPacket.decode bytes).map fun message => .testPacket message
  else none

theorem decode_encode (message : SesmPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode_nil]
  | loginRequest message => simp [decode, encode, tag, LoginRequest.decode_encode_nil]
  | loginResponse message => simp [decode, encode, tag, LoginResponse.decode_encode_nil]
  | synchronizationComplete message => simp [decode, encode, tag, SynchronizationComplete.decode_encode_nil]
  | retransmissionRequest message => simp [decode, encode, tag, RetransmissionRequest.decode_encode_nil]
  | logoutRequest message => simp [decode, encode, tag, LogoutRequest.decode_encode]
  | goodbyePacket message => simp [decode, encode, tag, GoodbyePacket.decode_encode]
  | tradingSessionUpdate message => simp [decode, encode, tag, TradingSessionUpdate.decode_encode_nil]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | clientHeartbeat message => simp [decode, encode, tag, ClientHeartbeat.decode_encode_nil]
  | testPacket message => simp [decode, encode, tag, TestPacket.decode_encode]

end SesmPayload

/-- Sesm Tcp Packet: the body, which the record carries with the proof it fits its frame -/
structure SesmTcpPacketBody where
  sesmPayload : SesmPayload
  deriving DecidableEq, Repr

namespace SesmTcpPacketBody

def encodeBody (message : SesmTcpPacketBody) : List UInt8 :=
  encodeUInt 1 (SesmPayload.tag message.sesmPayload)
    ++ (SesmPayload.encode message.sesmPayload)

def decodeBody (bytes : List UInt8) : Option SesmTcpPacketBody := do
  let (sesmPacketType, bytes) ← decodeUInt 1 bytes
  let sesmPayload ← SesmPayload.decode sesmPacketType bytes
  pure { sesmPayload }

theorem decodeBody_encodeBody (message : SesmTcpPacketBody) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SesmPayload.decode_encode, some_bind]
  rfl

end SesmTcpPacketBody

/-- Sesm Tcp Packet: the body with the proof its encoding fits Sesm Packet Length, whose 2 bytes no bound of the fields fits -/
abbrev SesmTcpPacket := Fitting SesmTcpPacketBody.encodeBody 0 65536

namespace SesmTcpPacket

def encode (message : SesmTcpPacket) : List UInt8 :=
  encodeFramedLE 2 0 SesmTcpPacketBody.encodeBody message.val

def decode : List UInt8 → Option (SesmTcpPacket × List UInt8) :=
  decodeFittingAllLE 2 0 SesmTcpPacketBody.encodeBody SesmTcpPacketBody.decodeBody

@[simp] theorem decode_encode (message : SesmTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAllLE_encodeFramedLE 2 0 SesmTcpPacketBody.encodeBody SesmTcpPacketBody.decodeBody message (SesmTcpPacketBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : SesmTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : SesmTcpPacket) : (encode message).length ≤ 65537 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramedLE_length]
  omega

end SesmTcpPacket

/-- Tcp Packet -/
structure TcpPacket where
  sesmTcpPacket : List SesmTcpPacket
  deriving DecidableEq, Repr

namespace TcpPacket

def encode (message : TcpPacket) : List UInt8 :=
  encodeMany SesmTcpPacket.encode message.sesmTcpPacket

def decode (bytes : List UInt8) : Option TcpPacket := do
  let sesmTcpPacket ← decodeAll SesmTcpPacket.decode bytes.length bytes
  pure { sesmTcpPacket }

theorem decode_encode (message : TcpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany SesmTcpPacket.encode SesmTcpPacket.decode SesmTcpPacket.decode_encode SesmTcpPacket.encode_length_pos message.sesmTcpPacket _ (encodeMany_length_ge SesmTcpPacket.encode SesmTcpPacket.encode_length_pos message.sesmTcpPacket), some_bind]
  rfl

end TcpPacket

end Omi.MiaxMiaxoptionsMpfMachV11Tcp
