import Omi.Wire

/-!
# Miami International Holdings Headers Only v1.0.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Esesm Packet Length is not an integer it reads.

Note: Unsequenced Data Packet is not framed: its length Esesm Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxPearlequitiesHeaderonlyEsesmV10A

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

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequenceNumber : BitVec 64
  matchingEngineId : BitVec 8
  sequencedMessageType : Alpha 2
  sequencedMessage : Capped 65499
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUInt 1 message.matchingEngineId
    ++ (Alpha.encode message.sequencedMessageType
    ++ (message.sequencedMessage.val)))

def decode (bytes : List UInt8) : Option SequencedDataPacket := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (matchingEngineId, bytes) ← decodeUInt 1 bytes
  let (sequencedMessageType, bytes) ← Alpha.decode 2 bytes
  let sequencedMessage_ := bytes
  if fits_sequencedMessage : sequencedMessage_.length ≤ 65499 then
    pure { sequenceNumber, matchingEngineId, sequencedMessageType, sequencedMessage := ⟨sequencedMessage_, fits_sequencedMessage⟩ }
  else none

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 65510 := by
  have bound_sequencedMessage := message.sequencedMessage.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

theorem decode_encode (message : SequencedDataPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sequencedMessage.length_le]
  rfl

end SequencedDataPacket

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessageType : Alpha 2
  unsequencedMessage : Capped 65499
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  Alpha.encode message.unsequencedMessageType
    ++ (message.unsequencedMessage.val)

def decode (bytes : List UInt8) : Option UnsequencedDataPacket := do
  let (unsequencedMessageType, bytes) ← Alpha.decode 2 bytes
  let unsequencedMessage_ := bytes
  if fits_unsequencedMessage : unsequencedMessage_.length ≤ 65499 then
    pure { unsequencedMessageType, unsequencedMessage := ⟨unsequencedMessage_, fits_unsequencedMessage⟩ }
  else none

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 65501 := by
  have bound_unsequencedMessage := message.unsequencedMessage.length_le
  unfold encode
  simp only [List.length_append, Alpha.encode_length]
  omega

theorem decode_encode (message : UnsequencedDataPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.unsequencedMessage.length_le]
  rfl

end UnsequencedDataPacket

/-- Login Request: 35 bytes -/
structure LoginRequest where
  esesmVersion : Alpha 5
  username : Alpha 5
  computerId : Alpha 8
  applicationProtocol : Alpha 8
  requestedTradingSessionId : BitVec 8
  requestedSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginRequest

def encode (message : LoginRequest) : List UInt8 :=
  Alpha.encode message.esesmVersion
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.computerId
    ++ (Alpha.encode message.applicationProtocol
    ++ (encodeUInt 1 message.requestedTradingSessionId
    ++ (encodeUIntLE 8 message.requestedSequenceNumber)))))

def decode (bytes : List UInt8) : Option (LoginRequest × List UInt8) := do
  let (esesmVersion, bytes) ← Alpha.decode 5 bytes
  let (username, bytes) ← Alpha.decode 5 bytes
  let (computerId, bytes) ← Alpha.decode 8 bytes
  let (applicationProtocol, bytes) ← Alpha.decode 8 bytes
  let (requestedTradingSessionId, bytes) ← decodeUInt 1 bytes
  let (requestedSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ esesmVersion, username, computerId, applicationProtocol, requestedTradingSessionId, requestedSequenceNumber }, bytes)

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
  logoutText : Capped 65499
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option LogoutRequest := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 65499 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogoutRequest) : (encode message).length ≤ 65500 := by
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
  logoutText : Capped 65499
  deriving DecidableEq, Repr

namespace GoodbyePacket

def encode (message : GoodbyePacket) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option GoodbyePacket := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 65499 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : GoodbyePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GoodbyePacket) : (encode message).length ≤ 65500 := by
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
  testText : Capped 65499
  deriving DecidableEq, Repr

namespace TestPacket

def encode (message : TestPacket) : List UInt8 :=
  message.testText.val

def decode (bytes : List UInt8) : Option TestPacket := do
  let testText_ := bytes
  if fits_testText : testText_.length ≤ 65499 then
    pure { testText := ⟨testText_, fits_testText⟩ }
  else none

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TestPacket) : (encode message).length ≤ 65499 := by
  have bound_testText := message.testText.length_le
  unfold encode
  omega

theorem decode_encode (message : TestPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [dite_eq_left message.testText.length_le]
  rfl

end TestPacket

/-- Any Esesm Payload, selected by Esesm Packet Type -/
inductive EsesmPayload where
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

namespace EsesmPayload

/-- The Esesm Packet Type each message is sent under -/
def tag : EsesmPayload → BitVec 8
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

def encode : EsesmPayload → List UInt8
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

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : EsesmPayload) : (encode message).length ≤ 65510 := by
  cases message with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | loginRequest inner =>
    simp only [encode, LoginRequest.encode_length]
    omega
  | loginResponse inner =>
    simp only [encode, LoginResponse.encode_length]
    omega
  | synchronizationComplete inner =>
    simp only [encode, SynchronizationComplete.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [encode, RetransmissionRequest.encode_length]
    omega
  | logoutRequest inner =>
    have bound_inner := LogoutRequest.encode_length_le inner
    simp only [encode]
    omega
  | goodbyePacket inner =>
    have bound_inner := GoodbyePacket.encode_length_le inner
    simp only [encode]
    omega
  | tradingSessionUpdate inner =>
    simp only [encode, TradingSessionUpdate.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | clientHeartbeat inner =>
    simp only [encode, ClientHeartbeat.encode_length]
    omega
  | testPacket inner =>
    have bound_inner := TestPacket.encode_length_le inner
    simp only [encode]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option EsesmPayload :=
  if tag = 115 then (SequencedDataPacket.decode bytes).map fun message => .sequencedDataPacket message
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).map fun message => .unsequencedDataPacket message
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

theorem decode_encode (message : EsesmPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode]
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

end EsesmPayload

/-- Esesm Tcp Packet -/
structure EsesmTcpPacket where
  esesmPayload : EsesmPayload
  deriving DecidableEq, Repr

namespace EsesmTcpPacket

def encodeBody (message : EsesmTcpPacket) : List UInt8 :=
  encodeUInt 1 (EsesmPayload.tag message.esesmPayload)
    ++ (EsesmPayload.encode message.esesmPayload)

def decodeBody (bytes : List UInt8) : Option EsesmTcpPacket := do
  let (esesmPacketType, bytes) ← decodeUInt 1 bytes
  let esesmPayload ← EsesmPayload.decode esesmPacketType bytes
  pure { esesmPayload }

theorem decodeBody_encodeBody (message : EsesmTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EsesmPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : EsesmTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.esesmPayload with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | loginRequest inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, LoginRequest.encode_length]
    omega
  | loginResponse inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, LoginResponse.encode_length]
    omega
  | synchronizationComplete inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, SynchronizationComplete.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, RetransmissionRequest.encode_length]
    omega
  | logoutRequest inner =>
    have bound_inner := LogoutRequest.encode_length_le inner
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | goodbyePacket inner =>
    have bound_inner := GoodbyePacket.encode_length_le inner
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | tradingSessionUpdate inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, TradingSessionUpdate.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | clientHeartbeat inner =>
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeat.encode_length]
    omega
  | testPacket inner =>
    have bound_inner := TestPacket.encode_length_le inner
    simp only [EsesmPayload.encode, List.length_append, encodeUInt_length]
    omega

/-- Size rule: Esesm Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : EsesmTcpPacket → List UInt8 :=
  encodeFramedLE 2 0 encodeBody

def decode : List UInt8 → Option (EsesmTcpPacket × List UInt8) :=
  decodeFramedAllLE 2 0 decodeBody

@[simp] theorem decode_encode (message : EsesmTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : EsesmTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end EsesmTcpPacket

/-- Packet -/
structure Packet where
  esesmTcpPacket : List EsesmTcpPacket
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany EsesmTcpPacket.encode message.esesmTcpPacket

def decode (bytes : List UInt8) : Option Packet := do
  let esesmTcpPacket ← decodeAll EsesmTcpPacket.decode bytes.length bytes
  pure { esesmTcpPacket }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany EsesmTcpPacket.encode EsesmTcpPacket.decode EsesmTcpPacket.decode_encode EsesmTcpPacket.encode_length_pos message.esesmTcpPacket _ (encodeMany_length_ge EsesmTcpPacket.encode EsesmTcpPacket.encode_length_pos message.esesmTcpPacket), some_bind]
  rfl

end Packet

end Omi.MiaxPearlequitiesHeaderonlyEsesmV10A
