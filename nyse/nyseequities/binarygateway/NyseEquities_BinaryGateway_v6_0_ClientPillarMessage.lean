import Wire

/-!
# New York Stock Exchange Binary Gateway v6.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NyseNyseequitiesBinarygatewayPillarstreamV60ClientPillarMessage

/-- Settlement Type: one byte code -/
def SettlementType.codes : List UInt8 :=
  [0x30, 0x31]

inductive SettlementType where
  | regularWay -- Regular Way
  | cash -- Cash
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementType

def toByte : SettlementType → UInt8
  | .regularWay => 0x30
  | .cash => 0x31
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementType :=
  if byte = 0x30 then .regularWay
  else .cash

def ofByte (byte : UInt8) : SettlementType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementType) : ofByte value.toByte = value := by
  cases value with
  | regularWay => decide
  | cash => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SettlementType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SettlementType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementType

/-- Risk User Type: one byte code -/
def RiskUserType.codes : List UInt8 :=
  [0x45, 0x43]

inductive RiskUserType where
  | enteringFirm -- Entering Firm
  | clearingFirm -- Clearing Firm
  | unlisted (byte : { byte : UInt8 // byte ∉ RiskUserType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RiskUserType

def toByte : RiskUserType → UInt8
  | .enteringFirm => 0x45
  | .clearingFirm => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RiskUserType :=
  if byte = 0x45 then .enteringFirm
  else .clearingFirm

def ofByte (byte : UInt8) : RiskUserType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RiskUserType) : ofByte value.toByte = value := by
  cases value with
  | enteringFirm => decide
  | clearingFirm => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RiskUserType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RiskUserType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RiskUserType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : RiskUserType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : RiskUserType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RiskUserType

/-- Login Message -/
structure LoginMessage where
  username : Alpha 16
  password : Alpha 32
  mic : Alpha 4
  version : Alpha 20
  deriving DecidableEq, Repr

namespace LoginMessage

def encodeBody (message : LoginMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.mic
    ++ (Alpha.encode message.version)))

def decodeBody (bytes : List UInt8) : Option (LoginMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 16 bytes
  let (password, bytes) ← Alpha.decode 32 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (version, bytes) ← Alpha.decode 20 bytes
  pure ({ username, password, mic, version }, bytes)

theorem decodeBody_encodeBody (message : LoginMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : LoginMessage) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : LoginMessage → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (LoginMessage × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : LoginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : LoginMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end LoginMessage

/-- Heartbeat -/
structure Heartbeat where
  deriving DecidableEq, Repr

namespace Heartbeat

def encodeBody (_ : Heartbeat) : List UInt8 :=
  []

def decodeBody (bytes : List UInt8) : Option (Heartbeat × List UInt8) :=
  some (⟨⟩, bytes)

theorem decodeBody_encodeBody (message : Heartbeat) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  simp [decodeBody, encodeBody]

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Heartbeat) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_nil]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : Heartbeat → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (Heartbeat × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : Heartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Heartbeat) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Heartbeat

/-- Stream Id: 8 bytes -/
structure StreamId where
  sess : BitVec 32
  value : BitVec 32
  deriving DecidableEq, Repr

namespace StreamId

def encode (message : StreamId) : List UInt8 :=
  encodeUIntLE 4 message.sess
    ++ (encodeUIntLE 4 message.value)

def decode (bytes : List UInt8) : Option (StreamId × List UInt8) := do
  let (sess, bytes) ← decodeUIntLE 4 bytes
  let (value, bytes) ← decodeUIntLE 4 bytes
  pure ({ sess, value }, bytes)

@[simp] theorem encode_length (message : StreamId) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : StreamId) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamId) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StreamId

/-- Open -/
structure Open where
  streamId : StreamId
  startSeq : BitVec 64
  endSeq : BitVec 64
  access : BitVec 8
  mode : BitVec 8
  deriving DecidableEq, Repr

namespace Open

def encodeBody (message : Open) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUIntLE 8 message.startSeq
    ++ (encodeUIntLE 8 message.endSeq
    ++ (encodeUInt 1 message.access
    ++ (encodeUInt 1 message.mode))))

def decodeBody (bytes : List UInt8) : Option (Open × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (startSeq, bytes) ← decodeUIntLE 8 bytes
  let (endSeq, bytes) ← decodeUIntLE 8 bytes
  let (access, bytes) ← decodeUInt 1 bytes
  let (mode, bytes) ← decodeUInt 1 bytes
  pure ({ streamId, startSeq, endSeq, access, mode }, bytes)

theorem decodeBody_encodeBody (message : Open) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Open) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, ← Nat.add_assoc, StreamId.encode_length, encodeUIntLE_length, encodeUInt_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : Open → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (Open × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : Open) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Open) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Open

/-- Close -/
structure Close where
  streamId : StreamId
  deriving DecidableEq, Repr

namespace Close

def encodeBody (message : Close) : List UInt8 :=
  StreamId.encode message.streamId

def decodeBody (bytes : List UInt8) : Option (Close × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  pure ({ streamId }, bytes)

theorem decodeBody_encodeBody (message : Close) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [StreamId.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Close) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [StreamId.encode_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : Close → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (Close × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : Close) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Close) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Close

/-- Seq Msg Id: 16 bytes -/
structure SeqMsgId where
  streamId : StreamId
  seq : BitVec 64
  deriving DecidableEq, Repr

namespace SeqMsgId

def encode (message : SeqMsgId) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUIntLE 8 message.seq)

def decode (bytes : List UInt8) : Option (SeqMsgId × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (seq, bytes) ← decodeUIntLE 8 bytes
  pure ({ streamId, seq }, bytes)

@[simp] theorem encode_length (message : SeqMsgId) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, StreamId.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SeqMsgId) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SeqMsgId) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SeqMsgId

/-- Session Configuration Request Message: 70 bytes -/
structure SessionConfigurationRequestMessage where
  username : Alpha 16
  cancelOnDisconnect : BitVec 8
  throttlePreference : BitVec 8
  selfTradePrevention : BitVec 8
  orderPriorityUpdateAckSubscription : BitVec 8
  boldDesignation : BitVec 8
  reserved49 : Alpha 49
  deriving DecidableEq, Repr

namespace SessionConfigurationRequestMessage

def encode (message : SessionConfigurationRequestMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (encodeUIntLE 1 message.cancelOnDisconnect
    ++ (encodeUIntLE 1 message.throttlePreference
    ++ (encodeUIntLE 1 message.selfTradePrevention
    ++ (encodeUIntLE 1 message.orderPriorityUpdateAckSubscription
    ++ (encodeUIntLE 1 message.boldDesignation
    ++ (Alpha.encode message.reserved49))))))

def decode (bytes : List UInt8) : Option (SessionConfigurationRequestMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 16 bytes
  let (cancelOnDisconnect, bytes) ← decodeUIntLE 1 bytes
  let (throttlePreference, bytes) ← decodeUIntLE 1 bytes
  let (selfTradePrevention, bytes) ← decodeUIntLE 1 bytes
  let (orderPriorityUpdateAckSubscription, bytes) ← decodeUIntLE 1 bytes
  let (boldDesignation, bytes) ← decodeUIntLE 1 bytes
  let (reserved49, bytes) ← Alpha.decode 49 bytes
  pure ({ username, cancelOnDisconnect, throttlePreference, selfTradePrevention, orderPriorityUpdateAckSubscription, boldDesignation, reserved49 }, bytes)

@[simp] theorem encode_length (message : SessionConfigurationRequestMessage) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SessionConfigurationRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionConfigurationRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SessionConfigurationRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SessionConfigurationRequestMessage

/-- Sequenced Filler Message: 0 bytes -/
structure SequencedFillerMessage where
  deriving DecidableEq, Repr

namespace SequencedFillerMessage

def encode (_ : SequencedFillerMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SequencedFillerMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SequencedFillerMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SequencedFillerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedFillerMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedFillerMessage

/-- Sub Msg Header: 4 bytes -/
structure SubMsgHeader where
  subMsgType : BitVec 16
  subMsgLength : BitVec 16
  deriving DecidableEq, Repr

namespace SubMsgHeader

def encode (message : SubMsgHeader) : List UInt8 :=
  encodeUIntLE 2 message.subMsgType
    ++ (encodeUIntLE 2 message.subMsgLength)

def decode (bytes : List UInt8) : Option (SubMsgHeader × List UInt8) := do
  let (subMsgType, bytes) ← decodeUIntLE 2 bytes
  let (subMsgLength, bytes) ← decodeUIntLE 2 bytes
  pure ({ subMsgType, subMsgLength }, bytes)

@[simp] theorem encode_length (message : SubMsgHeader) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SubMsgHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SubMsgHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SubMsgHeader

/-- Optional Order Add On: 41 bytes -/
structure OptionalOrderAddOn where
  subMsgHeader : SubMsgHeader
  deliverToCompId : Alpha 5
  maxFloor : BitVec 32
  locateBroker : Alpha 4
  reserved8 : Alpha 8
  offsetPrice : BitVec 64
  effectiveTime : BitVec 64
  deriving DecidableEq, Repr

namespace OptionalOrderAddOn

def encode (message : OptionalOrderAddOn) : List UInt8 :=
  SubMsgHeader.encode message.subMsgHeader
    ++ (Alpha.encode message.deliverToCompId
    ++ (encodeUIntLE 4 message.maxFloor
    ++ (Alpha.encode message.locateBroker
    ++ (Alpha.encode message.reserved8
    ++ (encodeUIntLE 8 message.offsetPrice
    ++ (encodeUIntLE 8 message.effectiveTime))))))

def decode (bytes : List UInt8) : Option (OptionalOrderAddOn × List UInt8) := do
  let (subMsgHeader, bytes) ← SubMsgHeader.decode bytes
  let (deliverToCompId, bytes) ← Alpha.decode 5 bytes
  let (maxFloor, bytes) ← decodeUIntLE 4 bytes
  let (locateBroker, bytes) ← Alpha.decode 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (offsetPrice, bytes) ← decodeUIntLE 8 bytes
  let (effectiveTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ subMsgHeader, deliverToCompId, maxFloor, locateBroker, reserved8, offsetPrice, effectiveTime }, bytes)

@[simp] theorem encode_length (message : OptionalOrderAddOn) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, SubMsgHeader.encode_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OptionalOrderAddOn) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionalOrderAddOn) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubMsgHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OptionalOrderAddOn) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OptionalOrderAddOn

/-- Optional Routing Strategy Add On: 32 bytes -/
structure OptionalRoutingStrategyAddOn where
  subMsgHeader : SubMsgHeader
  routingStrategy : BitVec 8
  reserved27 : Alpha 27
  deriving DecidableEq, Repr

namespace OptionalRoutingStrategyAddOn

def encode (message : OptionalRoutingStrategyAddOn) : List UInt8 :=
  SubMsgHeader.encode message.subMsgHeader
    ++ (encodeUIntLE 1 message.routingStrategy
    ++ (Alpha.encode message.reserved27))

def decode (bytes : List UInt8) : Option (OptionalRoutingStrategyAddOn × List UInt8) := do
  let (subMsgHeader, bytes) ← SubMsgHeader.decode bytes
  let (routingStrategy, bytes) ← decodeUIntLE 1 bytes
  let (reserved27, bytes) ← Alpha.decode 27 bytes
  pure ({ subMsgHeader, routingStrategy, reserved27 }, bytes)

@[simp] theorem encode_length (message : OptionalRoutingStrategyAddOn) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, SubMsgHeader.encode_length, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OptionalRoutingStrategyAddOn) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionalRoutingStrategyAddOn) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubMsgHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OptionalRoutingStrategyAddOn) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OptionalRoutingStrategyAddOn

/-- Optional Settlement Type Add On: 5 bytes -/
structure OptionalSettlementTypeAddOn where
  subMsgHeader : SubMsgHeader
  settlementType : SettlementType
  deriving DecidableEq, Repr

namespace OptionalSettlementTypeAddOn

def encode (message : OptionalSettlementTypeAddOn) : List UInt8 :=
  SubMsgHeader.encode message.subMsgHeader
    ++ (SettlementType.encode message.settlementType)

def decode (bytes : List UInt8) : Option (OptionalSettlementTypeAddOn × List UInt8) := do
  let (subMsgHeader, bytes) ← SubMsgHeader.decode bytes
  let (settlementType, bytes) ← SettlementType.decode bytes
  pure ({ subMsgHeader, settlementType }, bytes)

@[simp] theorem encode_length (message : OptionalSettlementTypeAddOn) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, SubMsgHeader.encode_length, SettlementType.encode_length]

theorem encode_length_pos (message : OptionalSettlementTypeAddOn) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionalSettlementTypeAddOn) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SubMsgHeader.decode_encode, some_bind]
  dsimp only
  rw [SettlementType.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OptionalSettlementTypeAddOn) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OptionalSettlementTypeAddOn

/-- The Optional Order Add On or Optional Routing Strategy Add On or Optional Settlement Type Add On the bytes left of New Order Single And Cancel Replace Request Message hold, or none -/
inductive NewOrderSingleAndCancelReplaceRequestMessageAppendage where
  | optionalOrderAddOn (message : OptionalOrderAddOn) -- 41 bytes
  | optionalRoutingStrategyAddOn (message : OptionalRoutingStrategyAddOn) -- 32 bytes
  | optionalSettlementTypeAddOn (message : OptionalSettlementTypeAddOn) -- 5 bytes
  | absent
  deriving DecidableEq, Repr

namespace NewOrderSingleAndCancelReplaceRequestMessageAppendage

def encode : NewOrderSingleAndCancelReplaceRequestMessageAppendage → List UInt8
  | .optionalOrderAddOn message => OptionalOrderAddOn.encode message
  | .optionalRoutingStrategyAddOn message => OptionalRoutingStrategyAddOn.encode message
  | .optionalSettlementTypeAddOn message => OptionalSettlementTypeAddOn.encode message
  | .absent => []

/-- Read by the bytes the frame has left: each add on takes its own number of them, and none takes none -/
def decode (bytes : List UInt8) : Option NewOrderSingleAndCancelReplaceRequestMessageAppendage :=
  if bytes.length = 41 then (OptionalOrderAddOn.decode bytes).map (fun read => .optionalOrderAddOn read.1)
  else
    if bytes.length = 32 then (OptionalRoutingStrategyAddOn.decode bytes).map (fun read => .optionalRoutingStrategyAddOn read.1)
    else
      if bytes.length = 5 then (OptionalSettlementTypeAddOn.decode bytes).map (fun read => .optionalSettlementTypeAddOn read.1)
      else
        if bytes.length = 0 then some .absent else none

@[simp] theorem decode_encode (message : NewOrderSingleAndCancelReplaceRequestMessageAppendage) : decode (encode message) = some message := by
  cases message with
  | optionalOrderAddOn inner =>
    have read := OptionalOrderAddOn.decode_encode_nil inner
    simp only [encode, decode, OptionalOrderAddOn.encode_length, read]
    rfl
  | optionalRoutingStrategyAddOn inner =>
    have read := OptionalRoutingStrategyAddOn.decode_encode_nil inner
    simp only [encode, decode, OptionalRoutingStrategyAddOn.encode_length, read]
    rfl
  | optionalSettlementTypeAddOn inner =>
    have read := OptionalSettlementTypeAddOn.decode_encode_nil inner
    simp only [encode, decode, OptionalSettlementTypeAddOn.encode_length, read]
    rfl
  | absent =>
    rfl

/-- The most bytes an add on can take, which is the largest of them -/
theorem encode_length_le (message : NewOrderSingleAndCancelReplaceRequestMessageAppendage) : (encode message).length ≤ 41 := by
  cases message with
  | optionalOrderAddOn inner =>
    simp only [encode, OptionalOrderAddOn.encode_length]
    omega
  | optionalRoutingStrategyAddOn inner =>
    simp only [encode, OptionalRoutingStrategyAddOn.encode_length]
    omega
  | optionalSettlementTypeAddOn inner =>
    simp only [encode, OptionalSettlementTypeAddOn.encode_length]
    omega
  | absent =>
    simp only [encode, List.length_nil]
    omega

end NewOrderSingleAndCancelReplaceRequestMessageAppendage

/-- New Order Single And Cancel Replace Request Message -/
structure NewOrderSingleAndCancelReplaceRequestMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  mmid : BitVec 32
  mpsubid1 : Alpha 1
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  bitfieldOrderInstructions : BitVec 64
  price : BitVec 64
  orderQty : BitVec 32
  minQty : BitVec 32
  userData : Alpha 8
  seqMsgLengthAppendage : NewOrderSingleAndCancelReplaceRequestMessageAppendage
  deriving DecidableEq, Repr

namespace NewOrderSingleAndCancelReplaceRequestMessage

def encode (message : NewOrderSingleAndCancelReplaceRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.mmid
    ++ (Alpha.encode message.mpsubid1
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.bitfieldOrderInstructions
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.minQty
    ++ (Alpha.encode message.userData
    ++ (NewOrderSingleAndCancelReplaceRequestMessageAppendage.encode message.seqMsgLengthAppendage)))))))))))

def decode (bytes : List UInt8) : Option NewOrderSingleAndCancelReplaceRequestMessage := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (mmid, bytes) ← decodeUIntLE 4 bytes
  let (mpsubid1, bytes) ← Alpha.decode 1 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (bitfieldOrderInstructions, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (userData, bytes) ← Alpha.decode 8 bytes
  let seqMsgLengthAppendage ← NewOrderSingleAndCancelReplaceRequestMessageAppendage.decode bytes
  pure { symbolId, mpid, mmid, mpsubid1, clOrdId, origClOrdId, bitfieldOrderInstructions, price, orderQty, minQty, userData, seqMsgLengthAppendage }

theorem encode_length_pos (message : NewOrderSingleAndCancelReplaceRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderSingleAndCancelReplaceRequestMessage) : (encode message).length ≤ 102 := by
  have bound_seqMsgLengthAppendage := NewOrderSingleAndCancelReplaceRequestMessageAppendage.encode_length_le message.seqMsgLengthAppendage
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length]
  omega

theorem decode_encode (message : NewOrderSingleAndCancelReplaceRequestMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [NewOrderSingleAndCancelReplaceRequestMessageAppendage.decode_encode, some_bind]
  rfl

end NewOrderSingleAndCancelReplaceRequestMessage

/-- Order Cancel Request Message: 24 bytes -/
structure OrderCancelRequestMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelRequestMessage

def encode (message : OrderCancelRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId)))

def decode (bytes : List UInt8) : Option (OrderCancelRequestMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbolId, mpid, clOrdId, origClOrdId }, bytes)

@[simp] theorem encode_length (message : OrderCancelRequestMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderCancelRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderCancelRequestMessage

/-- Order Modify Request Message: 30 bytes -/
structure OrderModifyRequestMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  orderQty : BitVec 32
  side : BitVec 8
  locateReqdU81 : BitVec 8
  deriving DecidableEq, Repr

namespace OrderModifyRequestMessage

def encode (message : OrderModifyRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 1 message.locateReqdU81))))))

def decode (bytes : List UInt8) : Option (OrderModifyRequestMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (locateReqdU81, bytes) ← decodeUIntLE 1 bytes
  pure ({ symbolId, mpid, clOrdId, origClOrdId, orderQty, side, locateReqdU81 }, bytes)

@[simp] theorem encode_length (message : OrderModifyRequestMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderModifyRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderModifyRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderModifyRequestMessage

/-- Bulk Cancel Request Message: 27 bytes -/
structure BulkCancelRequestMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  mmid : BitVec 32
  clOrdId : BitVec 64
  deliverToCompId : Alpha 5
  bulkCancelType : BitVec 8
  side : BitVec 8
  deriving DecidableEq, Repr

namespace BulkCancelRequestMessage

def encode (message : BulkCancelRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.mmid
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (Alpha.encode message.deliverToCompId
    ++ (encodeUIntLE 1 message.bulkCancelType
    ++ (encodeUIntLE 1 message.side))))))

def decode (bytes : List UInt8) : Option (BulkCancelRequestMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (mmid, bytes) ← decodeUIntLE 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (deliverToCompId, bytes) ← Alpha.decode 5 bytes
  let (bulkCancelType, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  pure ({ symbolId, mpid, mmid, clOrdId, deliverToCompId, bulkCancelType, side }, bytes)

@[simp] theorem encode_length (message : BulkCancelRequestMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : BulkCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkCancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BulkCancelRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end BulkCancelRequestMessage

/-- Symbol Subscription Request Message: 20 bytes -/
structure SymbolSubscriptionRequestMessage where
  symbolId : BitVec 32
  username : Alpha 16
  deriving DecidableEq, Repr

namespace SymbolSubscriptionRequestMessage

def encode (message : SymbolSubscriptionRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.username)

def decode (bytes : List UInt8) : Option (SymbolSubscriptionRequestMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (username, bytes) ← Alpha.decode 16 bytes
  pure ({ symbolId, username }, bytes)

@[simp] theorem encode_length (message : SymbolSubscriptionRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SymbolSubscriptionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolSubscriptionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SymbolSubscriptionRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SymbolSubscriptionRequestMessage

/-- Tg Begin Message: 0 bytes -/
structure TgBeginMessage where
  deriving DecidableEq, Repr

namespace TgBeginMessage

def encode (_ : TgBeginMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (TgBeginMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : TgBeginMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TgBeginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TgBeginMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TgBeginMessage

/-- Tg End Message: 0 bytes -/
structure TgEndMessage where
  deriving DecidableEq, Repr

namespace TgEndMessage

def encode (_ : TgEndMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (TgEndMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : TgEndMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TgEndMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TgEndMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TgEndMessage

/-- Manual Action Id: 16 bytes -/
structure ManualActionId where
  streamId : StreamId
  seq : BitVec 64
  deriving DecidableEq, Repr

namespace ManualActionId

def encode (message : ManualActionId) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUIntLE 8 message.seq)

def decode (bytes : List UInt8) : Option (ManualActionId × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (seq, bytes) ← decodeUIntLE 8 bytes
  pure ({ streamId, seq }, bytes)

@[simp] theorem encode_length (message : ManualActionId) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, StreamId.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ManualActionId) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ManualActionId) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ManualActionId

/-- Manual Action Response Message: 65 bytes -/
structure ManualActionResponseMessage where
  symbolId : BitVec 32
  clOrdId : BitVec 64
  manualActionId : ManualActionId
  sellIndicator : BitVec 8
  intradaySellShortQty : BitVec 32
  mpsubid1 : Alpha 1
  locateReqdU81 : BitVec 8
  selfTradeTypeBits : BitVec 8
  userData : Alpha 8
  manualResponseType : BitVec 8
  dmmRejectReason : Alpha 20
  deriving DecidableEq, Repr

namespace ManualActionResponseMessage

def encode (message : ManualActionResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (ManualActionId.encode message.manualActionId
    ++ (encodeUIntLE 1 message.sellIndicator
    ++ (encodeUIntLE 4 message.intradaySellShortQty
    ++ (Alpha.encode message.mpsubid1
    ++ (encodeUIntLE 1 message.locateReqdU81
    ++ (encodeUIntLE 1 message.selfTradeTypeBits
    ++ (Alpha.encode message.userData
    ++ (encodeUIntLE 1 message.manualResponseType
    ++ (Alpha.encode message.dmmRejectReason))))))))))

def decode (bytes : List UInt8) : Option (ManualActionResponseMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (manualActionId, bytes) ← ManualActionId.decode bytes
  let (sellIndicator, bytes) ← decodeUIntLE 1 bytes
  let (intradaySellShortQty, bytes) ← decodeUIntLE 4 bytes
  let (mpsubid1, bytes) ← Alpha.decode 1 bytes
  let (locateReqdU81, bytes) ← decodeUIntLE 1 bytes
  let (selfTradeTypeBits, bytes) ← decodeUIntLE 1 bytes
  let (userData, bytes) ← Alpha.decode 8 bytes
  let (manualResponseType, bytes) ← decodeUIntLE 1 bytes
  let (dmmRejectReason, bytes) ← Alpha.decode 20 bytes
  pure ({ symbolId, clOrdId, manualActionId, sellIndicator, intradaySellShortQty, mpsubid1, locateReqdU81, selfTradeTypeBits, userData, manualResponseType, dmmRejectReason }, bytes)

@[simp] theorem encode_length (message : ManualActionResponseMessage) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ManualActionId.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ManualActionResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ManualActionResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ManualActionId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ManualActionResponseMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ManualActionResponseMessage

/-- Risk Limit Update Request Message: 268 bytes -/
structure RiskLimitUpdateRequestMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMakerNul : Alpha 10
  mpsubid4 : Alpha 4
  reserved4 : Alpha 4
  clearingNumber : Alpha 5
  clOrdId : BitVec 64
  riskUserCrd : BitVec 32
  riskUserType : RiskUserType
  riskControlType : BitVec 8
  riskControlActivation : BitVec 8
  usdLimit : BitVec 64
  timeLimit : BitVec 32
  percentageLimit : BitVec 32
  countLimit : BitVec 32
  breachActionRequest : BitVec 8
  iocAttribution : BitVec 8
  riskRangeId : BitVec 8
  riskMinimumValue : BitVec 64
  priceScale : BitVec 8
  reserved190 : Alpha 190
  deriving DecidableEq, Repr

namespace RiskLimitUpdateRequestMessage

def encode (message : RiskLimitUpdateRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMakerNul
    ++ (Alpha.encode message.mpsubid4
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.clearingNumber
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.riskUserCrd
    ++ (RiskUserType.encode message.riskUserType
    ++ (encodeUIntLE 1 message.riskControlType
    ++ (encodeUIntLE 1 message.riskControlActivation
    ++ (encodeUIntLE 8 message.usdLimit
    ++ (encodeUIntLE 4 message.timeLimit
    ++ (encodeUIntLE 4 message.percentageLimit
    ++ (encodeUIntLE 4 message.countLimit
    ++ (encodeUIntLE 1 message.breachActionRequest
    ++ (encodeUIntLE 1 message.iocAttribution
    ++ (encodeUIntLE 1 message.riskRangeId
    ++ (encodeUIntLE 8 message.riskMinimumValue
    ++ (encodeUIntLE 1 message.priceScale
    ++ (Alpha.encode message.reserved190))))))))))))))))))))

def decode (bytes : List UInt8) : Option (RiskLimitUpdateRequestMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMakerNul, bytes) ← Alpha.decode 10 bytes
  let (mpsubid4, bytes) ← Alpha.decode 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (clearingNumber, bytes) ← Alpha.decode 5 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (riskUserCrd, bytes) ← decodeUIntLE 4 bytes
  let (riskUserType, bytes) ← RiskUserType.decode bytes
  let (riskControlType, bytes) ← decodeUIntLE 1 bytes
  let (riskControlActivation, bytes) ← decodeUIntLE 1 bytes
  let (usdLimit, bytes) ← decodeUIntLE 8 bytes
  let (timeLimit, bytes) ← decodeUIntLE 4 bytes
  let (percentageLimit, bytes) ← decodeUIntLE 4 bytes
  let (countLimit, bytes) ← decodeUIntLE 4 bytes
  let (breachActionRequest, bytes) ← decodeUIntLE 1 bytes
  let (iocAttribution, bytes) ← decodeUIntLE 1 bytes
  let (riskRangeId, bytes) ← decodeUIntLE 1 bytes
  let (riskMinimumValue, bytes) ← decodeUIntLE 8 bytes
  let (priceScale, bytes) ← decodeUIntLE 1 bytes
  let (reserved190, bytes) ← Alpha.decode 190 bytes
  pure ({ symbolId, mpid, marketMakerNul, mpsubid4, reserved4, clearingNumber, clOrdId, riskUserCrd, riskUserType, riskControlType, riskControlActivation, usdLimit, timeLimit, percentageLimit, countLimit, breachActionRequest, iocAttribution, riskRangeId, riskMinimumValue, priceScale, reserved190 }, bytes)

@[simp] theorem encode_length (message : RiskLimitUpdateRequestMessage) : (encode message).length = 268 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, RiskUserType.encode_length]

theorem encode_length_pos (message : RiskLimitUpdateRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskLimitUpdateRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, RiskUserType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RiskLimitUpdateRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RiskLimitUpdateRequestMessage

/-- Risk Action Request Message: 246 bytes -/
structure RiskActionRequestMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMakerNul : Alpha 10
  mpsubid4 : Alpha 4
  reserved4 : Alpha 4
  clearingNumber : Alpha 5
  clOrdId : BitVec 64
  riskUserCrd : BitVec 32
  riskUserType : RiskUserType
  riskControlType : BitVec 8
  riskActionType : BitVec 8
  riskRangeId : BitVec 8
  reserved199 : Alpha 199
  deriving DecidableEq, Repr

namespace RiskActionRequestMessage

def encode (message : RiskActionRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMakerNul
    ++ (Alpha.encode message.mpsubid4
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.clearingNumber
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.riskUserCrd
    ++ (RiskUserType.encode message.riskUserType
    ++ (encodeUIntLE 1 message.riskControlType
    ++ (encodeUIntLE 1 message.riskActionType
    ++ (encodeUIntLE 1 message.riskRangeId
    ++ (Alpha.encode message.reserved199))))))))))))

def decode (bytes : List UInt8) : Option (RiskActionRequestMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMakerNul, bytes) ← Alpha.decode 10 bytes
  let (mpsubid4, bytes) ← Alpha.decode 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (clearingNumber, bytes) ← Alpha.decode 5 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (riskUserCrd, bytes) ← decodeUIntLE 4 bytes
  let (riskUserType, bytes) ← RiskUserType.decode bytes
  let (riskControlType, bytes) ← decodeUIntLE 1 bytes
  let (riskActionType, bytes) ← decodeUIntLE 1 bytes
  let (riskRangeId, bytes) ← decodeUIntLE 1 bytes
  let (reserved199, bytes) ← Alpha.decode 199 bytes
  pure ({ symbolId, mpid, marketMakerNul, mpsubid4, reserved4, clearingNumber, clOrdId, riskUserCrd, riskUserType, riskControlType, riskActionType, riskRangeId, reserved199 }, bytes)

@[simp] theorem encode_length (message : RiskActionRequestMessage) : (encode message).length = 246 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, RiskUserType.encode_length]

theorem encode_length_pos (message : RiskActionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskActionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, RiskUserType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RiskActionRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RiskActionRequestMessage

/-- Any Client Sequenced Message, selected by Seq Msg Type -/
inductive ClientSequencedMessage where
  | sessionConfigurationRequestMessage (message : SessionConfigurationRequestMessage) -- 544
  | sequencedFillerMessage (message : SequencedFillerMessage) -- 642
  | newOrderSingleAndCancelReplaceRequestMessage (message : NewOrderSingleAndCancelReplaceRequestMessage) -- 576
  | orderCancelRequestMessage (message : OrderCancelRequestMessage) -- 640
  | orderModifyRequestMessage (message : OrderModifyRequestMessage) -- 624
  | bulkCancelRequestMessage (message : BulkCancelRequestMessage) -- 641
  | symbolSubscriptionRequestMessage (message : SymbolSubscriptionRequestMessage) -- 838
  | tgBeginMessage (message : TgBeginMessage) -- 835
  | tgEndMessage (message : TgEndMessage) -- 836
  | manualActionResponseMessage (message : ManualActionResponseMessage) -- 852
  | riskLimitUpdateRequestMessage (message : RiskLimitUpdateRequestMessage) -- 816
  | riskActionRequestMessage (message : RiskActionRequestMessage) -- 817
  deriving DecidableEq, Repr

namespace ClientSequencedMessage

/-- The Seq Msg Type each message is sent under -/
def tag : ClientSequencedMessage → BitVec 16
  | .sessionConfigurationRequestMessage _ => 544
  | .sequencedFillerMessage _ => 642
  | .newOrderSingleAndCancelReplaceRequestMessage _ => 576
  | .orderCancelRequestMessage _ => 640
  | .orderModifyRequestMessage _ => 624
  | .bulkCancelRequestMessage _ => 641
  | .symbolSubscriptionRequestMessage _ => 838
  | .tgBeginMessage _ => 835
  | .tgEndMessage _ => 836
  | .manualActionResponseMessage _ => 852
  | .riskLimitUpdateRequestMessage _ => 816
  | .riskActionRequestMessage _ => 817

def encode : ClientSequencedMessage → List UInt8
  | .sessionConfigurationRequestMessage message => SessionConfigurationRequestMessage.encode message
  | .sequencedFillerMessage message => SequencedFillerMessage.encode message
  | .newOrderSingleAndCancelReplaceRequestMessage message => NewOrderSingleAndCancelReplaceRequestMessage.encode message
  | .orderCancelRequestMessage message => OrderCancelRequestMessage.encode message
  | .orderModifyRequestMessage message => OrderModifyRequestMessage.encode message
  | .bulkCancelRequestMessage message => BulkCancelRequestMessage.encode message
  | .symbolSubscriptionRequestMessage message => SymbolSubscriptionRequestMessage.encode message
  | .tgBeginMessage message => TgBeginMessage.encode message
  | .tgEndMessage message => TgEndMessage.encode message
  | .manualActionResponseMessage message => ManualActionResponseMessage.encode message
  | .riskLimitUpdateRequestMessage message => RiskLimitUpdateRequestMessage.encode message
  | .riskActionRequestMessage message => RiskActionRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientSequencedMessage) : (encode message).length ≤ 268 := by
  cases message with
  | sessionConfigurationRequestMessage inner =>
    simp only [encode, SessionConfigurationRequestMessage.encode_length]
    omega
  | sequencedFillerMessage inner =>
    simp only [encode, SequencedFillerMessage.encode_length]
    omega
  | newOrderSingleAndCancelReplaceRequestMessage inner =>
    have bound_inner := NewOrderSingleAndCancelReplaceRequestMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderCancelRequestMessage inner =>
    simp only [encode, OrderCancelRequestMessage.encode_length]
    omega
  | orderModifyRequestMessage inner =>
    simp only [encode, OrderModifyRequestMessage.encode_length]
    omega
  | bulkCancelRequestMessage inner =>
    simp only [encode, BulkCancelRequestMessage.encode_length]
    omega
  | symbolSubscriptionRequestMessage inner =>
    simp only [encode, SymbolSubscriptionRequestMessage.encode_length]
    omega
  | tgBeginMessage inner =>
    simp only [encode, TgBeginMessage.encode_length]
    omega
  | tgEndMessage inner =>
    simp only [encode, TgEndMessage.encode_length]
    omega
  | manualActionResponseMessage inner =>
    simp only [encode, ManualActionResponseMessage.encode_length]
    omega
  | riskLimitUpdateRequestMessage inner =>
    simp only [encode, RiskLimitUpdateRequestMessage.encode_length]
    omega
  | riskActionRequestMessage inner =>
    simp only [encode, RiskActionRequestMessage.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option ClientSequencedMessage :=
  if tag = 544 then (SessionConfigurationRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sessionConfigurationRequestMessage message) else none
  else if tag = 642 then (SequencedFillerMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedFillerMessage message) else none
  else if tag = 576 then (NewOrderSingleAndCancelReplaceRequestMessage.decode bytes).map fun message => .newOrderSingleAndCancelReplaceRequestMessage message
  else if tag = 640 then (OrderCancelRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderCancelRequestMessage message) else none
  else if tag = 624 then (OrderModifyRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderModifyRequestMessage message) else none
  else if tag = 641 then (BulkCancelRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.bulkCancelRequestMessage message) else none
  else if tag = 838 then (SymbolSubscriptionRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.symbolSubscriptionRequestMessage message) else none
  else if tag = 835 then (TgBeginMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tgBeginMessage message) else none
  else if tag = 836 then (TgEndMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tgEndMessage message) else none
  else if tag = 852 then (ManualActionResponseMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.manualActionResponseMessage message) else none
  else if tag = 816 then (RiskLimitUpdateRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.riskLimitUpdateRequestMessage message) else none
  else if tag = 817 then (RiskActionRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.riskActionRequestMessage message) else none
  else none

theorem decode_encode (message : ClientSequencedMessage) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | sessionConfigurationRequestMessage message => simp [decode, encode, tag, SessionConfigurationRequestMessage.decode_encode_nil]
  | sequencedFillerMessage message => simp [decode, encode, tag, SequencedFillerMessage.decode_encode_nil]
  | newOrderSingleAndCancelReplaceRequestMessage message => simp [decode, encode, tag, NewOrderSingleAndCancelReplaceRequestMessage.decode_encode]
  | orderCancelRequestMessage message => simp [decode, encode, tag, OrderCancelRequestMessage.decode_encode_nil]
  | orderModifyRequestMessage message => simp [decode, encode, tag, OrderModifyRequestMessage.decode_encode_nil]
  | bulkCancelRequestMessage message => simp [decode, encode, tag, BulkCancelRequestMessage.decode_encode_nil]
  | symbolSubscriptionRequestMessage message => simp [decode, encode, tag, SymbolSubscriptionRequestMessage.decode_encode_nil]
  | tgBeginMessage message => simp [decode, encode, tag, TgBeginMessage.decode_encode_nil]
  | tgEndMessage message => simp [decode, encode, tag, TgEndMessage.decode_encode_nil]
  | manualActionResponseMessage message => simp [decode, encode, tag, ManualActionResponseMessage.decode_encode_nil]
  | riskLimitUpdateRequestMessage message => simp [decode, encode, tag, RiskLimitUpdateRequestMessage.decode_encode_nil]
  | riskActionRequestMessage message => simp [decode, encode, tag, RiskActionRequestMessage.decode_encode_nil]

end ClientSequencedMessage

/-- Client Seq Msg -/
structure ClientSeqMsg where
  seqMsgId : SeqMsgId
  reserved4 : Alpha 4
  timestamp : BitVec 64
  seqMsgLength : BitVec 16
  clientSequencedMessage : ClientSequencedMessage
  deriving DecidableEq, Repr

namespace ClientSeqMsg

def encodeBody (message : ClientSeqMsg) : List UInt8 :=
  SeqMsgId.encode message.seqMsgId
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 (ClientSequencedMessage.tag message.clientSequencedMessage)
    ++ (encodeUIntLE 2 message.seqMsgLength
    ++ (ClientSequencedMessage.encode message.clientSequencedMessage)))))

def decodeBody (bytes : List UInt8) : Option ClientSeqMsg := do
  let (seqMsgId, bytes) ← SeqMsgId.decode bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (seqMsgType, bytes) ← decodeUIntLE 2 bytes
  let (seqMsgLength, bytes) ← decodeUIntLE 2 bytes
  let clientSequencedMessage ← ClientSequencedMessage.decode seqMsgType bytes
  pure { seqMsgId, reserved4, timestamp, seqMsgLength, clientSequencedMessage }

theorem decodeBody_encodeBody (message : ClientSeqMsg) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [SeqMsgId.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ClientSequencedMessage.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientSeqMsg) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientSequencedMessage with
  | sessionConfigurationRequestMessage inner =>
    simp only [ClientSequencedMessage.encode, List.length_append, ← Nat.add_assoc, SeqMsgId.encode_length, Alpha.encode_length, encodeUIntLE_length, SessionConfigurationRequestMessage.encode_length]
    omega
  | sequencedFillerMessage inner =>
    simp only [ClientSequencedMessage.encode, List.length_append, ← Nat.add_assoc, SeqMsgId.encode_length, Alpha.encode_length, encodeUIntLE_length, SequencedFillerMessage.encode_length]
    omega
  | newOrderSingleAndCancelReplaceRequestMessage inner =>
    have bound_inner := NewOrderSingleAndCancelReplaceRequestMessage.encode_length_le inner
    simp only [ClientSequencedMessage.encode, List.length_append, ← Nat.add_assoc, SeqMsgId.encode_length, Alpha.encode_length, encodeUIntLE_length]
    omega
  | orderCancelRequestMessage inner =>
    simp only [ClientSequencedMessage.encode, List.length_append, ← Nat.add_assoc, SeqMsgId.encode_length, Alpha.encode_length, encodeUIntLE_length, OrderCancelRequestMessage.encode_length]
    omega
  | orderModifyRequestMessage inner =>
    simp only [ClientSequencedMessage.encode, List.length_append, ← Nat.add_assoc, SeqMsgId.encode_length, Alpha.encode_length, encodeUIntLE_length, OrderModifyRequestMessage.encode_length]
    omega
  | bulkCancelRequestMessage inner =>
    simp only [ClientSequencedMessage.encode, List.length_append, ← Nat.add_assoc, SeqMsgId.encode_length, Alpha.encode_length, encodeUIntLE_length, BulkCancelRequestMessage.encode_length]
    omega
  | symbolSubscriptionRequestMessage inner =>
    simp only [ClientSequencedMessage.encode, List.length_append, ← Nat.add_assoc, SeqMsgId.encode_length, Alpha.encode_length, encodeUIntLE_length, SymbolSubscriptionRequestMessage.encode_length]
    omega
  | tgBeginMessage inner =>
    simp only [ClientSequencedMessage.encode, List.length_append, ← Nat.add_assoc, SeqMsgId.encode_length, Alpha.encode_length, encodeUIntLE_length, TgBeginMessage.encode_length]
    omega
  | tgEndMessage inner =>
    simp only [ClientSequencedMessage.encode, List.length_append, ← Nat.add_assoc, SeqMsgId.encode_length, Alpha.encode_length, encodeUIntLE_length, TgEndMessage.encode_length]
    omega
  | manualActionResponseMessage inner =>
    simp only [ClientSequencedMessage.encode, List.length_append, ← Nat.add_assoc, SeqMsgId.encode_length, Alpha.encode_length, encodeUIntLE_length, ManualActionResponseMessage.encode_length]
    omega
  | riskLimitUpdateRequestMessage inner =>
    simp only [ClientSequencedMessage.encode, List.length_append, ← Nat.add_assoc, SeqMsgId.encode_length, Alpha.encode_length, encodeUIntLE_length, RiskLimitUpdateRequestMessage.encode_length]
    omega
  | riskActionRequestMessage inner =>
    simp only [ClientSequencedMessage.encode, List.length_append, ← Nat.add_assoc, SeqMsgId.encode_length, Alpha.encode_length, encodeUIntLE_length, RiskActionRequestMessage.encode_length]
    omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : ClientSeqMsg → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (ClientSeqMsg × List UInt8) :=
  decodeFramedAllLE 2 4 decodeBody

@[simp] theorem decode_encode (message : ClientSeqMsg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ClientSeqMsg) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end ClientSeqMsg

/-- Any Client Message, selected by Msg Type -/
inductive ClientMessage where
  | loginMessage (message : LoginMessage) -- 513
  | heartbeat (message : Heartbeat) -- 516
  | open_ (message : Open) -- 517
  | close (message : Close) -- 519
  | clientSeqMsg (message : ClientSeqMsg) -- 2309
  deriving DecidableEq, Repr

namespace ClientMessage

/-- The Msg Type each message is sent under -/
def tag : ClientMessage → BitVec 16
  | .loginMessage _ => 513
  | .heartbeat _ => 516
  | .open_ _ => 517
  | .close _ => 519
  | .clientSeqMsg _ => 2309

def encode : ClientMessage → List UInt8
  | .loginMessage message => LoginMessage.encode message
  | .heartbeat message => Heartbeat.encode message
  | .open_ message => Open.encode message
  | .close message => Close.encode message
  | .clientSeqMsg message => ClientSeqMsg.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientMessage × List UInt8) :=
  if tag = 513 then (LoginMessage.decode bytes).map fun (message, rest) => (.loginMessage message, rest)
  else if tag = 516 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 517 then (Open.decode bytes).map fun (message, rest) => (.open_ message, rest)
  else if tag = 519 then (Close.decode bytes).map fun (message, rest) => (.close message, rest)
  else if tag = 2309 then (ClientSeqMsg.decode bytes).map fun (message, rest) => (.clientSeqMsg message, rest)
  else none

@[simp] theorem decode_encode (message : ClientMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientMessage

/-- Client Pillar Message -/
structure ClientPillarMessage where
  clientMessage : ClientMessage
  deriving DecidableEq, Repr

namespace ClientPillarMessage

def encode (message : ClientPillarMessage) : List UInt8 :=
  encodeUIntLE 2 (ClientMessage.tag message.clientMessage)
    ++ (ClientMessage.encode message.clientMessage)

def decode (bytes : List UInt8) : Option (ClientPillarMessage × List UInt8) := do
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (clientMessage, bytes) ← ClientMessage.decode msgType bytes
  pure ({ clientMessage }, bytes)

theorem encode_length_pos (message : ClientPillarMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : ClientPillarMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ClientMessage.decode_encode, some_bind]
  rfl

end ClientPillarMessage

end Omi.NyseNyseequitiesBinarygatewayPillarstreamV60ClientPillarMessage
