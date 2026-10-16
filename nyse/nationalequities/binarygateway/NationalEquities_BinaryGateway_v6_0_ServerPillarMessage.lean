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

namespace Omi.NyseNationalequitiesBinarygatewayPillarstreamV60ServerPillarMessage

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

/-- Login Response -/
structure LoginResponse where
  username : Alpha 16
  status : BitVec 8
  deriving DecidableEq, Repr

namespace LoginResponse

def encodeBody (message : LoginResponse) : List UInt8 :=
  Alpha.encode message.username
    ++ (encodeUInt 1 message.status)

def decodeBody (bytes : List UInt8) : Option (LoginResponse × List UInt8) := do
  let (username, bytes) ← Alpha.decode 16 bytes
  let (status, bytes) ← decodeUInt 1 bytes
  pure ({ username, status }, bytes)

theorem decodeBody_encodeBody (message : LoginResponse) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : LoginResponse) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : LoginResponse → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (LoginResponse × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : LoginResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : LoginResponse) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end LoginResponse

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

/-- Stream Avail -/
structure StreamAvail where
  streamId : StreamId
  nextSeq : BitVec 64
  access : BitVec 8
  deriving DecidableEq, Repr

namespace StreamAvail

def encodeBody (message : StreamAvail) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUIntLE 8 message.nextSeq
    ++ (encodeUInt 1 message.access))

def decodeBody (bytes : List UInt8) : Option (StreamAvail × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (nextSeq, bytes) ← decodeUIntLE 8 bytes
  let (access, bytes) ← decodeUInt 1 bytes
  pure ({ streamId, nextSeq, access }, bytes)

theorem decodeBody_encodeBody (message : StreamAvail) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : StreamAvail) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, ← Nat.add_assoc, StreamId.encode_length, encodeUIntLE_length, encodeUInt_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : StreamAvail → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (StreamAvail × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : StreamAvail) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : StreamAvail) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end StreamAvail

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

/-- Open Response -/
structure OpenResponse where
  streamId : StreamId
  status : BitVec 8
  access : BitVec 8
  deriving DecidableEq, Repr

namespace OpenResponse

def encodeBody (message : OpenResponse) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUInt 1 message.status
    ++ (encodeUInt 1 message.access))

def decodeBody (bytes : List UInt8) : Option (OpenResponse × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (status, bytes) ← decodeUInt 1 bytes
  let (access, bytes) ← decodeUInt 1 bytes
  pure ({ streamId, status, access }, bytes)

theorem decodeBody_encodeBody (message : OpenResponse) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : OpenResponse) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, ← Nat.add_assoc, StreamId.encode_length, encodeUInt_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : OpenResponse → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (OpenResponse × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : OpenResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : OpenResponse) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end OpenResponse

/-- Close Response -/
structure CloseResponse where
  streamId : StreamId
  status : BitVec 8
  deriving DecidableEq, Repr

namespace CloseResponse

def encodeBody (message : CloseResponse) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUInt 1 message.status)

def decodeBody (bytes : List UInt8) : Option (CloseResponse × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (status, bytes) ← decodeUInt 1 bytes
  pure ({ streamId, status }, bytes)

theorem decodeBody_encodeBody (message : CloseResponse) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : CloseResponse) : (encodeBody message).length + 4 < 256 ^ 2 := by
  unfold encodeBody
  simp only [List.length_append, StreamId.encode_length, encodeUInt_length]
  omega

/-- Size rule: Msg Length counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : CloseResponse → List UInt8 :=
  encodeFramedLE 2 4 encodeBody

def decode : List UInt8 → Option (CloseResponse × List UInt8) :=
  decodeFramedLE 2 4 decodeBody

@[simp] theorem decode_encode (message : CloseResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : CloseResponse) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end CloseResponse

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

/-- Equities Symbol Reference Data Message: 52 bytes -/
structure EquitiesSymbolReferenceDataMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  nyseSymbol : Alpha 24
  listedMic : Alpha 4
  roundLotSize : BitVec 8
  advRiskRangeId : BitVec 8
  reserved7 : Alpha 7
  mpvClassId : BitVec 16
  testSymbolIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace EquitiesSymbolReferenceDataMessage

def encode (message : EquitiesSymbolReferenceDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.nyseSymbol
    ++ (Alpha.encode message.listedMic
    ++ (encodeUIntLE 1 message.roundLotSize
    ++ (encodeUIntLE 1 message.advRiskRangeId
    ++ (Alpha.encode message.reserved7
    ++ (encodeUIntLE 2 message.mpvClassId
    ++ (encodeUIntLE 1 message.testSymbolIndicator))))))))

def decode (bytes : List UInt8) : Option (EquitiesSymbolReferenceDataMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (nyseSymbol, bytes) ← Alpha.decode 24 bytes
  let (listedMic, bytes) ← Alpha.decode 4 bytes
  let (roundLotSize, bytes) ← decodeUIntLE 1 bytes
  let (advRiskRangeId, bytes) ← decodeUIntLE 1 bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  let (mpvClassId, bytes) ← decodeUIntLE 2 bytes
  let (testSymbolIndicator, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, symbolId, nyseSymbol, listedMic, roundLotSize, advRiskRangeId, reserved7, mpvClassId, testSymbolIndicator }, bytes)

@[simp] theorem encode_length (message : EquitiesSymbolReferenceDataMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : EquitiesSymbolReferenceDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquitiesSymbolReferenceDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
theorem decode_encode_nil (message : EquitiesSymbolReferenceDataMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EquitiesSymbolReferenceDataMessage

/-- Dmm Symbol Reference Data Message: 125 bytes -/
structure DmmSymbolReferenceDataMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  nyseSymbol : Alpha 24
  book : Alpha 8
  mpid : Alpha 4
  dmmUnitNum : Alpha 3
  post : Alpha 2
  medianVolume : BitVec 64
  rdSeq : BitVec 64
  ridgePrice : BitVec 64
  ppp1 : BitVec 64
  ppp2 : BitVec 64
  ppp3 : BitVec 64
  openOnTradeMaxQty : BitVec 64
  closeOnTradeMaxQty : BitVec 64
  lmocp : BitVec 64
  deriving DecidableEq, Repr

namespace DmmSymbolReferenceDataMessage

def encode (message : DmmSymbolReferenceDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.nyseSymbol
    ++ (Alpha.encode message.book
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.dmmUnitNum
    ++ (Alpha.encode message.post
    ++ (encodeUIntLE 8 message.medianVolume
    ++ (encodeUIntLE 8 message.rdSeq
    ++ (encodeUIntLE 8 message.ridgePrice
    ++ (encodeUIntLE 8 message.ppp1
    ++ (encodeUIntLE 8 message.ppp2
    ++ (encodeUIntLE 8 message.ppp3
    ++ (encodeUIntLE 8 message.openOnTradeMaxQty
    ++ (encodeUIntLE 8 message.closeOnTradeMaxQty
    ++ (encodeUIntLE 8 message.lmocp)))))))))))))))

def decode (bytes : List UInt8) : Option (DmmSymbolReferenceDataMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (nyseSymbol, bytes) ← Alpha.decode 24 bytes
  let (book, bytes) ← Alpha.decode 8 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (dmmUnitNum, bytes) ← Alpha.decode 3 bytes
  let (post, bytes) ← Alpha.decode 2 bytes
  let (medianVolume, bytes) ← decodeUIntLE 8 bytes
  let (rdSeq, bytes) ← decodeUIntLE 8 bytes
  let (ridgePrice, bytes) ← decodeUIntLE 8 bytes
  let (ppp1, bytes) ← decodeUIntLE 8 bytes
  let (ppp2, bytes) ← decodeUIntLE 8 bytes
  let (ppp3, bytes) ← decodeUIntLE 8 bytes
  let (openOnTradeMaxQty, bytes) ← decodeUIntLE 8 bytes
  let (closeOnTradeMaxQty, bytes) ← decodeUIntLE 8 bytes
  let (lmocp, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, symbolId, nyseSymbol, book, mpid, dmmUnitNum, post, medianVolume, rdSeq, ridgePrice, ppp1, ppp2, ppp3, openOnTradeMaxQty, closeOnTradeMaxQty, lmocp }, bytes)

@[simp] theorem encode_length (message : DmmSymbolReferenceDataMessage) : (encode message).length = 125 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : DmmSymbolReferenceDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DmmSymbolReferenceDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DmmSymbolReferenceDataMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DmmSymbolReferenceDataMessage

/-- Minimum Price Variant Class Reference Data Message: 46 bytes -/
structure MinimumPriceVariantClassReferenceDataMessage where
  transactTime : BitVec 64
  mpvClassName : Alpha 20
  mpvClassId : BitVec 16
  rpimpv : BitVec 64
  luldmpv : BitVec 64
  deriving DecidableEq, Repr

namespace MinimumPriceVariantClassReferenceDataMessage

def encode (message : MinimumPriceVariantClassReferenceDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (Alpha.encode message.mpvClassName
    ++ (encodeUIntLE 2 message.mpvClassId
    ++ (encodeUIntLE 8 message.rpimpv
    ++ (encodeUIntLE 8 message.luldmpv))))

def decode (bytes : List UInt8) : Option (MinimumPriceVariantClassReferenceDataMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (mpvClassName, bytes) ← Alpha.decode 20 bytes
  let (mpvClassId, bytes) ← decodeUIntLE 2 bytes
  let (rpimpv, bytes) ← decodeUIntLE 8 bytes
  let (luldmpv, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, mpvClassName, mpvClassId, rpimpv, luldmpv }, bytes)

@[simp] theorem encode_length (message : MinimumPriceVariantClassReferenceDataMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MinimumPriceVariantClassReferenceDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinimumPriceVariantClassReferenceDataMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MinimumPriceVariantClassReferenceDataMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MinimumPriceVariantClassReferenceDataMessage

/-- Mpv Level Definition: 50 bytes -/
structure MpvLevelDefinition where
  mpvLevelName : Alpha 24
  price : BitVec 64
  quotingMpv : BitVec 64
  tradingMpv : BitVec 64
  mpvClassId : BitVec 16
  deriving DecidableEq, Repr

namespace MpvLevelDefinition

def encode (message : MpvLevelDefinition) : List UInt8 :=
  Alpha.encode message.mpvLevelName
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.quotingMpv
    ++ (encodeUIntLE 8 message.tradingMpv
    ++ (encodeUIntLE 2 message.mpvClassId))))

def decode (bytes : List UInt8) : Option (MpvLevelDefinition × List UInt8) := do
  let (mpvLevelName, bytes) ← Alpha.decode 24 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quotingMpv, bytes) ← decodeUIntLE 8 bytes
  let (tradingMpv, bytes) ← decodeUIntLE 8 bytes
  let (mpvClassId, bytes) ← decodeUIntLE 2 bytes
  pure ({ mpvLevelName, price, quotingMpv, tradingMpv, mpvClassId }, bytes)

@[simp] theorem encode_length (message : MpvLevelDefinition) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MpvLevelDefinition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MpvLevelDefinition) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MpvLevelDefinition

/-- Minimum Price Variant Level Reference Data Message -/
structure MinimumPriceVariantLevelReferenceDataMessage where
  transactTime : BitVec 64
  mpvLevelDefinition : List MpvLevelDefinition
  deriving DecidableEq, Repr

namespace MinimumPriceVariantLevelReferenceDataMessage

def encode (message : MinimumPriceVariantLevelReferenceDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeMany MpvLevelDefinition.encode message.mpvLevelDefinition)

def decode (bytes : List UInt8) : Option MinimumPriceVariantLevelReferenceDataMessage := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let mpvLevelDefinition ← decodeAll MpvLevelDefinition.decode bytes.length bytes
  pure { transactTime, mpvLevelDefinition }

theorem encode_length_pos (message : MinimumPriceVariantLevelReferenceDataMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

theorem decode_encode (message : MinimumPriceVariantLevelReferenceDataMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeAll_encodeMany MpvLevelDefinition.encode MpvLevelDefinition.decode MpvLevelDefinition.decode_encode MpvLevelDefinition.encode_length_pos message.mpvLevelDefinition _ (encodeMany_length_ge MpvLevelDefinition.encode MpvLevelDefinition.encode_length_pos message.mpvLevelDefinition), some_bind]
  rfl

end MinimumPriceVariantLevelReferenceDataMessage

/-- Mpid Configuration Message: 79 bytes -/
structure MpidConfigurationMessage where
  transactTime : BitVec 64
  mpidStatus : BitVec 8
  mpid : Alpha 4
  username : Alpha 16
  reserved50 : Alpha 50
  deriving DecidableEq, Repr

namespace MpidConfigurationMessage

def encode (message : MpidConfigurationMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.mpidStatus
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.reserved50))))

def decode (bytes : List UInt8) : Option (MpidConfigurationMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (mpidStatus, bytes) ← decodeUIntLE 1 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (username, bytes) ← Alpha.decode 16 bytes
  let (reserved50, bytes) ← Alpha.decode 50 bytes
  pure ({ transactTime, mpidStatus, mpid, username, reserved50 }, bytes)

@[simp] theorem encode_length (message : MpidConfigurationMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MpidConfigurationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MpidConfigurationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MpidConfigurationMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MpidConfigurationMessage

/-- Mmid Configuration Message: 138 bytes -/
structure MmidConfigurationMessage where
  transactTime : BitVec 64
  marketMaker : Alpha 10
  mmid : BitVec 32
  username : Alpha 16
  reserved100 : Alpha 100
  deriving DecidableEq, Repr

namespace MmidConfigurationMessage

def encode (message : MmidConfigurationMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (Alpha.encode message.marketMaker
    ++ (encodeUIntLE 4 message.mmid
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.reserved100))))

def decode (bytes : List UInt8) : Option (MmidConfigurationMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (marketMaker, bytes) ← Alpha.decode 10 bytes
  let (mmid, bytes) ← decodeUIntLE 4 bytes
  let (username, bytes) ← Alpha.decode 16 bytes
  let (reserved100, bytes) ← Alpha.decode 100 bytes
  pure ({ transactTime, marketMaker, mmid, username, reserved100 }, bytes)

@[simp] theorem encode_length (message : MmidConfigurationMessage) : (encode message).length = 138 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MmidConfigurationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmidConfigurationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MmidConfigurationMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MmidConfigurationMessage

/-- Session Configuration Acknowledgement Message: 94 bytes -/
structure SessionConfigurationAcknowledgementMessage where
  transactTime : BitVec 64
  userSessionType : BitVec 8
  userSessionStatus : BitVec 8
  username : Alpha 16
  mic : Alpha 4
  cancelOnDisconnect : BitVec 8
  throttlePreference : BitVec 8
  throttleWindow : BitVec 16
  throttleThreshold : BitVec 16
  symbolEligibility : BitVec 8
  maxOrderQuantity : BitVec 32
  selfTradePrevention : BitVec 8
  orderPriorityUpdateAckSubscription : BitVec 8
  ackStatus : BitVec 8
  boldDesignation : BitVec 8
  reserved49 : Alpha 49
  deriving DecidableEq, Repr

namespace SessionConfigurationAcknowledgementMessage

def encode (message : SessionConfigurationAcknowledgementMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.userSessionType
    ++ (encodeUIntLE 1 message.userSessionStatus
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.mic
    ++ (encodeUIntLE 1 message.cancelOnDisconnect
    ++ (encodeUIntLE 1 message.throttlePreference
    ++ (encodeUIntLE 2 message.throttleWindow
    ++ (encodeUIntLE 2 message.throttleThreshold
    ++ (encodeUIntLE 1 message.symbolEligibility
    ++ (encodeUIntLE 4 message.maxOrderQuantity
    ++ (encodeUIntLE 1 message.selfTradePrevention
    ++ (encodeUIntLE 1 message.orderPriorityUpdateAckSubscription
    ++ (encodeUIntLE 1 message.ackStatus
    ++ (encodeUIntLE 1 message.boldDesignation
    ++ (Alpha.encode message.reserved49)))))))))))))))

def decode (bytes : List UInt8) : Option (SessionConfigurationAcknowledgementMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (userSessionType, bytes) ← decodeUIntLE 1 bytes
  let (userSessionStatus, bytes) ← decodeUIntLE 1 bytes
  let (username, bytes) ← Alpha.decode 16 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (cancelOnDisconnect, bytes) ← decodeUIntLE 1 bytes
  let (throttlePreference, bytes) ← decodeUIntLE 1 bytes
  let (throttleWindow, bytes) ← decodeUIntLE 2 bytes
  let (throttleThreshold, bytes) ← decodeUIntLE 2 bytes
  let (symbolEligibility, bytes) ← decodeUIntLE 1 bytes
  let (maxOrderQuantity, bytes) ← decodeUIntLE 4 bytes
  let (selfTradePrevention, bytes) ← decodeUIntLE 1 bytes
  let (orderPriorityUpdateAckSubscription, bytes) ← decodeUIntLE 1 bytes
  let (ackStatus, bytes) ← decodeUIntLE 1 bytes
  let (boldDesignation, bytes) ← decodeUIntLE 1 bytes
  let (reserved49, bytes) ← Alpha.decode 49 bytes
  pure ({ transactTime, userSessionType, userSessionStatus, username, mic, cancelOnDisconnect, throttlePreference, throttleWindow, throttleThreshold, symbolEligibility, maxOrderQuantity, selfTradePrevention, orderPriorityUpdateAckSubscription, ackStatus, boldDesignation, reserved49 }, bytes)

@[simp] theorem encode_length (message : SessionConfigurationAcknowledgementMessage) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SessionConfigurationAcknowledgementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionConfigurationAcknowledgementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
theorem decode_encode_nil (message : SessionConfigurationAcknowledgementMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SessionConfigurationAcknowledgementMessage

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

/-- The Optional Order Add On or Optional Routing Strategy Add On or Optional Settlement Type Add On the bytes left of Order And Cancel Replace Acknowledgement Message hold, or none -/
inductive OrderAndCancelReplaceAcknowledgementMessageAppendage where
  | optionalOrderAddOn (message : OptionalOrderAddOn) -- 41 bytes
  | optionalRoutingStrategyAddOn (message : OptionalRoutingStrategyAddOn) -- 32 bytes
  | optionalSettlementTypeAddOn (message : OptionalSettlementTypeAddOn) -- 5 bytes
  | absent
  deriving DecidableEq, Repr

namespace OrderAndCancelReplaceAcknowledgementMessageAppendage

def encode : OrderAndCancelReplaceAcknowledgementMessageAppendage → List UInt8
  | .optionalOrderAddOn message => OptionalOrderAddOn.encode message
  | .optionalRoutingStrategyAddOn message => OptionalRoutingStrategyAddOn.encode message
  | .optionalSettlementTypeAddOn message => OptionalSettlementTypeAddOn.encode message
  | .absent => []

/-- Read by the bytes the frame has left: each add on takes its own number of them, and none takes none -/
def decode (bytes : List UInt8) : Option OrderAndCancelReplaceAcknowledgementMessageAppendage :=
  if bytes.length = 41 then (OptionalOrderAddOn.decode bytes).map (fun read => .optionalOrderAddOn read.1)
  else
    if bytes.length = 32 then (OptionalRoutingStrategyAddOn.decode bytes).map (fun read => .optionalRoutingStrategyAddOn read.1)
    else
      if bytes.length = 5 then (OptionalSettlementTypeAddOn.decode bytes).map (fun read => .optionalSettlementTypeAddOn read.1)
      else
        if bytes.length = 0 then some .absent else none

@[simp] theorem decode_encode (message : OrderAndCancelReplaceAcknowledgementMessageAppendage) : decode (encode message) = some message := by
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
theorem encode_length_le (message : OrderAndCancelReplaceAcknowledgementMessageAppendage) : (encode message).length ≤ 41 := by
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

end OrderAndCancelReplaceAcknowledgementMessageAppendage

/-- Order And Cancel Replace Acknowledgement Message -/
structure OrderAndCancelReplaceAcknowledgementMessage where
  transactTime : BitVec 64
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
  orderId : BitVec 64
  leavesQty : BitVec 32
  workingPrice : BitVec 64
  workingAwayFromDisplay : BitVec 8
  preLiquidityIndicator : Alpha 4
  reasonCode : BitVec 16
  ackType : BitVec 8
  bitfieldFlowIndicator : BitVec 8
  userData : Alpha 8
  seqMsgLengthAppendage : OrderAndCancelReplaceAcknowledgementMessageAppendage
  deriving DecidableEq, Repr

namespace OrderAndCancelReplaceAcknowledgementMessage

def encode (message : OrderAndCancelReplaceAcknowledgementMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.mmid
    ++ (Alpha.encode message.mpsubid1
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.bitfieldOrderInstructions
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 8 message.workingPrice
    ++ (encodeUIntLE 1 message.workingAwayFromDisplay
    ++ (Alpha.encode message.preLiquidityIndicator
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (encodeUIntLE 1 message.ackType
    ++ (encodeUIntLE 1 message.bitfieldFlowIndicator
    ++ (Alpha.encode message.userData
    ++ (OrderAndCancelReplaceAcknowledgementMessageAppendage.encode message.seqMsgLengthAppendage))))))))))))))))))))

def decode (bytes : List UInt8) : Option OrderAndCancelReplaceAcknowledgementMessage := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
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
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (workingPrice, bytes) ← decodeUIntLE 8 bytes
  let (workingAwayFromDisplay, bytes) ← decodeUIntLE 1 bytes
  let (preLiquidityIndicator, bytes) ← Alpha.decode 4 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (ackType, bytes) ← decodeUIntLE 1 bytes
  let (bitfieldFlowIndicator, bytes) ← decodeUIntLE 1 bytes
  let (userData, bytes) ← Alpha.decode 8 bytes
  let seqMsgLengthAppendage ← OrderAndCancelReplaceAcknowledgementMessageAppendage.decode bytes
  pure { transactTime, symbolId, mpid, mmid, mpsubid1, clOrdId, origClOrdId, bitfieldOrderInstructions, price, orderQty, minQty, orderId, leavesQty, workingPrice, workingAwayFromDisplay, preLiquidityIndicator, reasonCode, ackType, bitfieldFlowIndicator, userData, seqMsgLengthAppendage }

theorem encode_length_pos (message : OrderAndCancelReplaceAcknowledgementMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderAndCancelReplaceAcknowledgementMessage) : (encode message).length ≤ 139 := by
  have bound_seqMsgLengthAppendage := OrderAndCancelReplaceAcknowledgementMessageAppendage.encode_length_le message.seqMsgLengthAppendage
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length]
  omega

theorem decode_encode (message : OrderAndCancelReplaceAcknowledgementMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [OrderAndCancelReplaceAcknowledgementMessageAppendage.decode_encode, some_bind]
  rfl

end OrderAndCancelReplaceAcknowledgementMessage

/-- Order Modify Cancel Request Acknowledgment And Urout Message: 70 bytes -/
structure OrderModifyCancelRequestAcknowledgmentAndUroutMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  mpid : Alpha 4
  orderId : BitVec 64
  refClOrdId : BitVec 64
  origClOrdId : BitVec 64
  price : BitVec 64
  orderQty : BitVec 32
  leavesQty : BitVec 32
  side : BitVec 8
  locateReqdU81 : BitVec 8
  reasonCode : BitVec 16
  ackType : BitVec 8
  bitfieldFlowIndicator : BitVec 8
  userData : Alpha 8
  deriving DecidableEq, Repr

namespace OrderModifyCancelRequestAcknowledgmentAndUroutMessage

def encode (message : OrderModifyCancelRequestAcknowledgmentAndUroutMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.refClOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 1 message.locateReqdU81
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (encodeUIntLE 1 message.ackType
    ++ (encodeUIntLE 1 message.bitfieldFlowIndicator
    ++ (Alpha.encode message.userData))))))))))))))

def decode (bytes : List UInt8) : Option (OrderModifyCancelRequestAcknowledgmentAndUroutMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (refClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (locateReqdU81, bytes) ← decodeUIntLE 1 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (ackType, bytes) ← decodeUIntLE 1 bytes
  let (bitfieldFlowIndicator, bytes) ← decodeUIntLE 1 bytes
  let (userData, bytes) ← Alpha.decode 8 bytes
  pure ({ transactTime, symbolId, mpid, orderId, refClOrdId, origClOrdId, price, orderQty, leavesQty, side, locateReqdU81, reasonCode, ackType, bitfieldFlowIndicator, userData }, bytes)

@[simp] theorem encode_length (message : OrderModifyCancelRequestAcknowledgmentAndUroutMessage) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderModifyCancelRequestAcknowledgmentAndUroutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyCancelRequestAcknowledgmentAndUroutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
theorem decode_encode_nil (message : OrderModifyCancelRequestAcknowledgmentAndUroutMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderModifyCancelRequestAcknowledgmentAndUroutMessage

/-- Order Priority Update Acknowledgment Message: 58 bytes -/
structure OrderPriorityUpdateAcknowledgmentMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  mpid : Alpha 4
  orderId : BitVec 64
  clOrdId : BitVec 64
  workingPrice : BitVec 64
  orderQty : BitVec 32
  workingAwayFromDisplay : BitVec 8
  preLiquidityIndicator : Alpha 4
  ackType : BitVec 8
  userData : Alpha 8
  deriving DecidableEq, Repr

namespace OrderPriorityUpdateAcknowledgmentMessage

def encode (message : OrderPriorityUpdateAcknowledgmentMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.workingPrice
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 1 message.workingAwayFromDisplay
    ++ (Alpha.encode message.preLiquidityIndicator
    ++ (encodeUIntLE 1 message.ackType
    ++ (Alpha.encode message.userData))))))))))

def decode (bytes : List UInt8) : Option (OrderPriorityUpdateAcknowledgmentMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (workingPrice, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (workingAwayFromDisplay, bytes) ← decodeUIntLE 1 bytes
  let (preLiquidityIndicator, bytes) ← Alpha.decode 4 bytes
  let (ackType, bytes) ← decodeUIntLE 1 bytes
  let (userData, bytes) ← Alpha.decode 8 bytes
  pure ({ transactTime, symbolId, mpid, orderId, clOrdId, workingPrice, orderQty, workingAwayFromDisplay, preLiquidityIndicator, ackType, userData }, bytes)

@[simp] theorem encode_length (message : OrderPriorityUpdateAcknowledgmentMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderPriorityUpdateAcknowledgmentMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderPriorityUpdateAcknowledgmentMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
theorem decode_encode_nil (message : OrderPriorityUpdateAcknowledgmentMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderPriorityUpdateAcknowledgmentMessage

/-- The Optional Settlement Type Add On the bytes left of Execution Report Message hold, or none -/
inductive ExecutionReportMessageAppendage where
  | optionalSettlementTypeAddOn (message : OptionalSettlementTypeAddOn) -- 5 bytes
  | absent
  deriving DecidableEq, Repr

namespace ExecutionReportMessageAppendage

def encode : ExecutionReportMessageAppendage → List UInt8
  | .optionalSettlementTypeAddOn message => OptionalSettlementTypeAddOn.encode message
  | .absent => []

/-- Read by the bytes the frame has left: each add on takes its own number of them, and none takes none -/
def decode (bytes : List UInt8) : Option ExecutionReportMessageAppendage :=
  if bytes.length = 5 then (OptionalSettlementTypeAddOn.decode bytes).map (fun read => .optionalSettlementTypeAddOn read.1)
  else
    if bytes.length = 0 then some .absent else none

@[simp] theorem decode_encode (message : ExecutionReportMessageAppendage) : decode (encode message) = some message := by
  cases message with
  | optionalSettlementTypeAddOn inner =>
    have read := OptionalSettlementTypeAddOn.decode_encode_nil inner
    simp only [encode, decode, OptionalSettlementTypeAddOn.encode_length, read]
    rfl
  | absent =>
    rfl

/-- The most bytes an add on can take, which is the largest of them -/
theorem encode_length_le (message : ExecutionReportMessageAppendage) : (encode message).length ≤ 5 := by
  cases message with
  | optionalSettlementTypeAddOn inner =>
    simp only [encode, OptionalSettlementTypeAddOn.encode_length]
    omega
  | absent =>
    simp only [encode, List.length_nil]
    omega

end ExecutionReportMessageAppendage

/-- Execution Report Message -/
structure ExecutionReportMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  mpid : Alpha 4
  orderId : BitVec 64
  clOrdId : BitVec 64
  dealId : BitVec 64
  lastPx : BitVec 64
  leavesQty : BitVec 32
  cumQty : BitVec 32
  lastQty : BitVec 32
  liquidityIndicator : Alpha 4
  bitfieldExecutionDetails : BitVec 8
  reserved3 : Alpha 3
  locateReqdU81 : BitVec 8
  participantType : BitVec 8
  reasonCode : BitVec 16
  userData : Alpha 8
  seqMsgLengthAppendage : ExecutionReportMessageAppendage
  deriving DecidableEq, Repr

namespace ExecutionReportMessage

def encode (message : ExecutionReportMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.dealId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.lastQty
    ++ (Alpha.encode message.liquidityIndicator
    ++ (encodeUIntLE 1 message.bitfieldExecutionDetails
    ++ (Alpha.encode message.reserved3
    ++ (encodeUIntLE 1 message.locateReqdU81
    ++ (encodeUIntLE 1 message.participantType
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (Alpha.encode message.userData
    ++ (ExecutionReportMessageAppendage.encode message.seqMsgLengthAppendage)))))))))))))))))

def decode (bytes : List UInt8) : Option ExecutionReportMessage := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (dealId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (liquidityIndicator, bytes) ← Alpha.decode 4 bytes
  let (bitfieldExecutionDetails, bytes) ← decodeUIntLE 1 bytes
  let (reserved3, bytes) ← Alpha.decode 3 bytes
  let (locateReqdU81, bytes) ← decodeUIntLE 1 bytes
  let (participantType, bytes) ← decodeUIntLE 1 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (userData, bytes) ← Alpha.decode 8 bytes
  let seqMsgLengthAppendage ← ExecutionReportMessageAppendage.decode bytes
  pure { transactTime, symbolId, mpid, orderId, clOrdId, dealId, lastPx, leavesQty, cumQty, lastQty, liquidityIndicator, bitfieldExecutionDetails, reserved3, locateReqdU81, participantType, reasonCode, userData, seqMsgLengthAppendage }

theorem encode_length_pos (message : ExecutionReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportMessage) : (encode message).length ≤ 85 := by
  have bound_seqMsgLengthAppendage := ExecutionReportMessageAppendage.encode_length_le message.seqMsgLengthAppendage
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length]
  omega

theorem decode_encode (message : ExecutionReportMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [ExecutionReportMessageAppendage.decode_encode, some_bind]
  rfl

end ExecutionReportMessage

/-- Ref Seq Msg Id: 16 bytes -/
structure RefSeqMsgId where
  streamId : StreamId
  seq : BitVec 64
  deriving DecidableEq, Repr

namespace RefSeqMsgId

def encode (message : RefSeqMsgId) : List UInt8 :=
  StreamId.encode message.streamId
    ++ (encodeUIntLE 8 message.seq)

def decode (bytes : List UInt8) : Option (RefSeqMsgId × List UInt8) := do
  let (streamId, bytes) ← StreamId.decode bytes
  let (seq, bytes) ← decodeUIntLE 8 bytes
  pure ({ streamId, seq }, bytes)

@[simp] theorem encode_length (message : RefSeqMsgId) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, StreamId.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : RefSeqMsgId) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefSeqMsgId) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, StreamId.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RefSeqMsgId

/-- Trade Bust Correct Message: 78 bytes -/
structure TradeBustCorrectMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  mpid : Alpha 4
  orderId : BitVec 64
  clOrdId : BitVec 64
  refSeqMsgId : RefSeqMsgId
  dealId : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 32
  reasonCode : BitVec 16
  userData : Alpha 8
  deriving DecidableEq, Repr

namespace TradeBustCorrectMessage

def encode (message : TradeBustCorrectMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (RefSeqMsgId.encode message.refSeqMsgId
    ++ (encodeUIntLE 8 message.dealId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (Alpha.encode message.userData))))))))))

def decode (bytes : List UInt8) : Option (TradeBustCorrectMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (refSeqMsgId, bytes) ← RefSeqMsgId.decode bytes
  let (dealId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (userData, bytes) ← Alpha.decode 8 bytes
  pure ({ transactTime, symbolId, mpid, orderId, clOrdId, refSeqMsgId, dealId, lastPx, lastQty, reasonCode, userData }, bytes)

@[simp] theorem encode_length (message : TradeBustCorrectMessage) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, RefSeqMsgId.encode_length]

theorem encode_length_pos (message : TradeBustCorrectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustCorrectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, RefSeqMsgId.decode_encode, some_bind]
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
theorem decode_encode_nil (message : TradeBustCorrectMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradeBustCorrectMessage

/-- Application Layer Reject Message: 39 bytes -/
structure ApplicationLayerRejectMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  mpid : Alpha 4
  clOrdId : BitVec 64
  reasonCode : BitVec 16
  rejectType : BitVec 8
  userData : Alpha 8
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace ApplicationLayerRejectMessage

def encode (message : ApplicationLayerRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 2 message.reasonCode
    ++ (encodeUIntLE 1 message.rejectType
    ++ (Alpha.encode message.userData
    ++ (Alpha.encode message.reserved4)))))))

def decode (bytes : List UInt8) : Option (ApplicationLayerRejectMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (reasonCode, bytes) ← decodeUIntLE 2 bytes
  let (rejectType, bytes) ← decodeUIntLE 1 bytes
  let (userData, bytes) ← Alpha.decode 8 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ transactTime, symbolId, mpid, clOrdId, reasonCode, rejectType, userData, reserved4 }, bytes)

@[simp] theorem encode_length (message : ApplicationLayerRejectMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ApplicationLayerRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ApplicationLayerRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ApplicationLayerRejectMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ApplicationLayerRejectMessage

/-- Symbol Subscription Acknowledgement Message: 29 bytes -/
structure SymbolSubscriptionAcknowledgementMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  username : Alpha 16
  subscriptionStatus : BitVec 8
  deriving DecidableEq, Repr

namespace SymbolSubscriptionAcknowledgementMessage

def encode (message : SymbolSubscriptionAcknowledgementMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.username
    ++ (encodeUIntLE 1 message.subscriptionStatus)))

def decode (bytes : List UInt8) : Option (SymbolSubscriptionAcknowledgementMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (username, bytes) ← Alpha.decode 16 bytes
  let (subscriptionStatus, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, symbolId, username, subscriptionStatus }, bytes)

@[simp] theorem encode_length (message : SymbolSubscriptionAcknowledgementMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SymbolSubscriptionAcknowledgementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolSubscriptionAcknowledgementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SymbolSubscriptionAcknowledgementMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SymbolSubscriptionAcknowledgementMessage

/-- Gt Begin Message: 8 bytes -/
structure GtBeginMessage where
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace GtBeginMessage

def encode (message : GtBeginMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (GtBeginMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime }, bytes)

@[simp] theorem encode_length (message : GtBeginMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : GtBeginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GtBeginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : GtBeginMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end GtBeginMessage

/-- Gt End Message: 8 bytes -/
structure GtEndMessage where
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace GtEndMessage

def encode (message : GtEndMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (GtEndMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime }, bytes)

@[simp] theorem encode_length (message : GtEndMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : GtEndMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GtEndMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : GtEndMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end GtEndMessage

/-- Auction Price Data Message: 42 bytes -/
structure AuctionPriceDataMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  imbalanceSide : BitVec 8
  sideOfUnpairedQty : BitVec 8
  imbalanceVolume : BitVec 32
  price : BitVec 64
  pairedQty : BitVec 32
  unpairedQty : BitVec 32
  buyDmmAvailableQty : BitVec 32
  sellDmmAvailableQty : BitVec 32
  deriving DecidableEq, Repr

namespace AuctionPriceDataMessage

def encode (message : AuctionPriceDataMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 1 message.imbalanceSide
    ++ (encodeUIntLE 1 message.sideOfUnpairedQty
    ++ (encodeUIntLE 4 message.imbalanceVolume
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.pairedQty
    ++ (encodeUIntLE 4 message.unpairedQty
    ++ (encodeUIntLE 4 message.buyDmmAvailableQty
    ++ (encodeUIntLE 4 message.sellDmmAvailableQty)))))))))

def decode (bytes : List UInt8) : Option (AuctionPriceDataMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (imbalanceSide, bytes) ← decodeUIntLE 1 bytes
  let (sideOfUnpairedQty, bytes) ← decodeUIntLE 1 bytes
  let (imbalanceVolume, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (pairedQty, bytes) ← decodeUIntLE 4 bytes
  let (unpairedQty, bytes) ← decodeUIntLE 4 bytes
  let (buyDmmAvailableQty, bytes) ← decodeUIntLE 4 bytes
  let (sellDmmAvailableQty, bytes) ← decodeUIntLE 4 bytes
  pure ({ transactTime, symbolId, imbalanceSide, sideOfUnpairedQty, imbalanceVolume, price, pairedQty, unpairedQty, buyDmmAvailableQty, sellDmmAvailableQty }, bytes)

@[simp] theorem encode_length (message : AuctionPriceDataMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AuctionPriceDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionPriceDataMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : AuctionPriceDataMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end AuctionPriceDataMessage

/-- Auction Request Message: 21 bytes -/
structure AuctionRequestMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  auctionType : BitVec 8
  ssrFilingPrice : BitVec 64
  deriving DecidableEq, Repr

namespace AuctionRequestMessage

def encode (message : AuctionRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 1 message.auctionType
    ++ (encodeUIntLE 8 message.ssrFilingPrice)))

def decode (bytes : List UInt8) : Option (AuctionRequestMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (auctionType, bytes) ← decodeUIntLE 1 bytes
  let (ssrFilingPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, symbolId, auctionType, ssrFilingPrice }, bytes)

@[simp] theorem encode_length (message : AuctionRequestMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AuctionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : AuctionRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end AuctionRequestMessage

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

/-- Manual Action Request Message: 91 bytes -/
structure ManualActionRequestMessage where
  transactTime : BitVec 64
  symbolId : BitVec 32
  introducingBadgeId : Alpha 4
  mpid : Alpha 4
  mmid : BitVec 32
  manualActionId : ManualActionId
  side : BitVec 8
  price : BitVec 64
  dmmRequestedQty : BitVec 32
  dmmAvailableQty : BitVec 32
  dmmAllocatedQty : BitVec 32
  ssrFilingPrice : BitVec 64
  manualOverride : BitVec 8
  manualOverrideReason : Alpha 20
  manualActionType : BitVec 8
  deriving DecidableEq, Repr

namespace ManualActionRequestMessage

def encode (message : ManualActionRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.introducingBadgeId
    ++ (Alpha.encode message.mpid
    ++ (encodeUIntLE 4 message.mmid
    ++ (ManualActionId.encode message.manualActionId
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.dmmRequestedQty
    ++ (encodeUIntLE 4 message.dmmAvailableQty
    ++ (encodeUIntLE 4 message.dmmAllocatedQty
    ++ (encodeUIntLE 8 message.ssrFilingPrice
    ++ (encodeUIntLE 1 message.manualOverride
    ++ (Alpha.encode message.manualOverrideReason
    ++ (encodeUIntLE 1 message.manualActionType))))))))))))))

def decode (bytes : List UInt8) : Option (ManualActionRequestMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (introducingBadgeId, bytes) ← Alpha.decode 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (mmid, bytes) ← decodeUIntLE 4 bytes
  let (manualActionId, bytes) ← ManualActionId.decode bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (dmmRequestedQty, bytes) ← decodeUIntLE 4 bytes
  let (dmmAvailableQty, bytes) ← decodeUIntLE 4 bytes
  let (dmmAllocatedQty, bytes) ← decodeUIntLE 4 bytes
  let (ssrFilingPrice, bytes) ← decodeUIntLE 8 bytes
  let (manualOverride, bytes) ← decodeUIntLE 1 bytes
  let (manualOverrideReason, bytes) ← Alpha.decode 20 bytes
  let (manualActionType, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, symbolId, introducingBadgeId, mpid, mmid, manualActionId, side, price, dmmRequestedQty, dmmAvailableQty, dmmAllocatedQty, ssrFilingPrice, manualOverride, manualOverrideReason, manualActionType }, bytes)

@[simp] theorem encode_length (message : ManualActionRequestMessage) : (encode message).length = 91 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ManualActionId.encode_length]

theorem encode_length_pos (message : ManualActionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ManualActionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ManualActionId.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ManualActionRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ManualActionRequestMessage

/-- Risk Control Acknowledgement Message: 310 bytes -/
structure RiskControlAcknowledgementMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMakerNul : Alpha 10
  mpsubid4 : Alpha 4
  reserved4 : Alpha 4
  clearingNumber : Alpha 5
  clOrdId : BitVec 64
  riskAckType : BitVec 8
  riskUserCrd : BitVec 32
  riskUserType : RiskUserType
  riskControlType : BitVec 8
  riskControlActivation : BitVec 8
  riskActionType : BitVec 8
  usdLimit : BitVec 64
  timeLimit : BitVec 32
  percentageLimit : BitVec 32
  countLimit : BitVec 32
  breachActionResponse : BitVec 8
  iocAttribution : BitVec 8
  usdCalculation1 : BitVec 64
  usdCalculation2 : BitVec 64
  usdCalculation3 : BitVec 64
  usdCalculation4 : BitVec 64
  countCalculation : BitVec 32
  blockedByBreachIndicator : BitVec 8
  blockedByKillSwitchIndicator : BitVec 8
  reinstatementRequiredBySelf : BitVec 8
  reinstatementRequiredByOther : BitVec 8
  riskRangeId : BitVec 8
  riskMinimumValue : BitVec 64
  priceScale : BitVec 8
  reserved190 : Alpha 190
  deriving DecidableEq, Repr

namespace RiskControlAcknowledgementMessage

def encode (message : RiskControlAcknowledgementMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMakerNul
    ++ (Alpha.encode message.mpsubid4
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.clearingNumber
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 1 message.riskAckType
    ++ (encodeUIntLE 4 message.riskUserCrd
    ++ (RiskUserType.encode message.riskUserType
    ++ (encodeUIntLE 1 message.riskControlType
    ++ (encodeUIntLE 1 message.riskControlActivation
    ++ (encodeUIntLE 1 message.riskActionType
    ++ (encodeUIntLE 8 message.usdLimit
    ++ (encodeUIntLE 4 message.timeLimit
    ++ (encodeUIntLE 4 message.percentageLimit
    ++ (encodeUIntLE 4 message.countLimit
    ++ (encodeUIntLE 1 message.breachActionResponse
    ++ (encodeUIntLE 1 message.iocAttribution
    ++ (encodeUIntLE 8 message.usdCalculation1
    ++ (encodeUIntLE 8 message.usdCalculation2
    ++ (encodeUIntLE 8 message.usdCalculation3
    ++ (encodeUIntLE 8 message.usdCalculation4
    ++ (encodeUIntLE 4 message.countCalculation
    ++ (encodeUIntLE 1 message.blockedByBreachIndicator
    ++ (encodeUIntLE 1 message.blockedByKillSwitchIndicator
    ++ (encodeUIntLE 1 message.reinstatementRequiredBySelf
    ++ (encodeUIntLE 1 message.reinstatementRequiredByOther
    ++ (encodeUIntLE 1 message.riskRangeId
    ++ (encodeUIntLE 8 message.riskMinimumValue
    ++ (encodeUIntLE 1 message.priceScale
    ++ (Alpha.encode message.reserved190)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RiskControlAcknowledgementMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMakerNul, bytes) ← Alpha.decode 10 bytes
  let (mpsubid4, bytes) ← Alpha.decode 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (clearingNumber, bytes) ← Alpha.decode 5 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (riskAckType, bytes) ← decodeUIntLE 1 bytes
  let (riskUserCrd, bytes) ← decodeUIntLE 4 bytes
  let (riskUserType, bytes) ← RiskUserType.decode bytes
  let (riskControlType, bytes) ← decodeUIntLE 1 bytes
  let (riskControlActivation, bytes) ← decodeUIntLE 1 bytes
  let (riskActionType, bytes) ← decodeUIntLE 1 bytes
  let (usdLimit, bytes) ← decodeUIntLE 8 bytes
  let (timeLimit, bytes) ← decodeUIntLE 4 bytes
  let (percentageLimit, bytes) ← decodeUIntLE 4 bytes
  let (countLimit, bytes) ← decodeUIntLE 4 bytes
  let (breachActionResponse, bytes) ← decodeUIntLE 1 bytes
  let (iocAttribution, bytes) ← decodeUIntLE 1 bytes
  let (usdCalculation1, bytes) ← decodeUIntLE 8 bytes
  let (usdCalculation2, bytes) ← decodeUIntLE 8 bytes
  let (usdCalculation3, bytes) ← decodeUIntLE 8 bytes
  let (usdCalculation4, bytes) ← decodeUIntLE 8 bytes
  let (countCalculation, bytes) ← decodeUIntLE 4 bytes
  let (blockedByBreachIndicator, bytes) ← decodeUIntLE 1 bytes
  let (blockedByKillSwitchIndicator, bytes) ← decodeUIntLE 1 bytes
  let (reinstatementRequiredBySelf, bytes) ← decodeUIntLE 1 bytes
  let (reinstatementRequiredByOther, bytes) ← decodeUIntLE 1 bytes
  let (riskRangeId, bytes) ← decodeUIntLE 1 bytes
  let (riskMinimumValue, bytes) ← decodeUIntLE 8 bytes
  let (priceScale, bytes) ← decodeUIntLE 1 bytes
  let (reserved190, bytes) ← Alpha.decode 190 bytes
  pure ({ symbolId, mpid, marketMakerNul, mpsubid4, reserved4, clearingNumber, clOrdId, riskAckType, riskUserCrd, riskUserType, riskControlType, riskControlActivation, riskActionType, usdLimit, timeLimit, percentageLimit, countLimit, breachActionResponse, iocAttribution, usdCalculation1, usdCalculation2, usdCalculation3, usdCalculation4, countCalculation, blockedByBreachIndicator, blockedByKillSwitchIndicator, reinstatementRequiredBySelf, reinstatementRequiredByOther, riskRangeId, riskMinimumValue, priceScale, reserved190 }, bytes)

@[simp] theorem encode_length (message : RiskControlAcknowledgementMessage) : (encode message).length = 310 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, RiskUserType.encode_length]

theorem encode_length_pos (message : RiskControlAcknowledgementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RiskControlAcknowledgementMessage) (rest : List UInt8) :
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
theorem decode_encode_nil (message : RiskControlAcknowledgementMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RiskControlAcknowledgementMessage

/-- Risk Control Alert Message: 301 bytes -/
structure RiskControlAlertMessage where
  symbolId : BitVec 32
  mpid : Alpha 4
  marketMakerNul : Alpha 10
  mpsubid4 : Alpha 4
  reserved4 : Alpha 4
  clearingNumber : Alpha 5
  riskUserCrd : BitVec 32
  riskUserType : RiskUserType
  riskControlType : BitVec 8
  usdLimit : BitVec 64
  timeLimit : BitVec 32
  percentageLimit : BitVec 32
  countLimit : BitVec 32
  breachActionResponse : BitVec 8
  iocAttribution : BitVec 8
  usdCalculation1 : BitVec 64
  usdCalculation2 : BitVec 64
  usdCalculation3 : BitVec 64
  usdCalculation4 : BitVec 64
  countCalculation : BitVec 32
  riskActionType : BitVec 8
  thresholdBreachLevel : BitVec 8
  blockedByBreachIndicator : BitVec 8
  blockedByKillSwitchIndicator : BitVec 8
  reinstatementRequiredBySelf : BitVec 8
  reinstatementRequiredByOther : BitVec 8
  reserved200 : Alpha 200
  deriving DecidableEq, Repr

namespace RiskControlAlertMessage

def encode (message : RiskControlAlertMessage) : List UInt8 :=
  encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.marketMakerNul
    ++ (Alpha.encode message.mpsubid4
    ++ (Alpha.encode message.reserved4
    ++ (Alpha.encode message.clearingNumber
    ++ (encodeUIntLE 4 message.riskUserCrd
    ++ (RiskUserType.encode message.riskUserType
    ++ (encodeUIntLE 1 message.riskControlType
    ++ (encodeUIntLE 8 message.usdLimit
    ++ (encodeUIntLE 4 message.timeLimit
    ++ (encodeUIntLE 4 message.percentageLimit
    ++ (encodeUIntLE 4 message.countLimit
    ++ (encodeUIntLE 1 message.breachActionResponse
    ++ (encodeUIntLE 1 message.iocAttribution
    ++ (encodeUIntLE 8 message.usdCalculation1
    ++ (encodeUIntLE 8 message.usdCalculation2
    ++ (encodeUIntLE 8 message.usdCalculation3
    ++ (encodeUIntLE 8 message.usdCalculation4
    ++ (encodeUIntLE 4 message.countCalculation
    ++ (encodeUIntLE 1 message.riskActionType
    ++ (encodeUIntLE 1 message.thresholdBreachLevel
    ++ (encodeUIntLE 1 message.blockedByBreachIndicator
    ++ (encodeUIntLE 1 message.blockedByKillSwitchIndicator
    ++ (encodeUIntLE 1 message.reinstatementRequiredBySelf
    ++ (encodeUIntLE 1 message.reinstatementRequiredByOther
    ++ (Alpha.encode message.reserved200))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RiskControlAlertMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (marketMakerNul, bytes) ← Alpha.decode 10 bytes
  let (mpsubid4, bytes) ← Alpha.decode 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (clearingNumber, bytes) ← Alpha.decode 5 bytes
  let (riskUserCrd, bytes) ← decodeUIntLE 4 bytes
  let (riskUserType, bytes) ← RiskUserType.decode bytes
  let (riskControlType, bytes) ← decodeUIntLE 1 bytes
  let (usdLimit, bytes) ← decodeUIntLE 8 bytes
  let (timeLimit, bytes) ← decodeUIntLE 4 bytes
  let (percentageLimit, bytes) ← decodeUIntLE 4 bytes
  let (countLimit, bytes) ← decodeUIntLE 4 bytes
  let (breachActionResponse, bytes) ← decodeUIntLE 1 bytes
  let (iocAttribution, bytes) ← decodeUIntLE 1 bytes
  let (usdCalculation1, bytes) ← decodeUIntLE 8 bytes
  let (usdCalculation2, bytes) ← decodeUIntLE 8 bytes
  let (usdCalculation3, bytes) ← decodeUIntLE 8 bytes
  let (usdCalculation4, bytes) ← decodeUIntLE 8 bytes
  let (countCalculation, bytes) ← decodeUIntLE 4 bytes
  let (riskActionType, bytes) ← decodeUIntLE 1 bytes
  let (thresholdBreachLevel, bytes) ← decodeUIntLE 1 bytes
  let (blockedByBreachIndicator, bytes) ← decodeUIntLE 1 bytes
  let (blockedByKillSwitchIndicator, bytes) ← decodeUIntLE 1 bytes
  let (reinstatementRequiredBySelf, bytes) ← decodeUIntLE 1 bytes
  let (reinstatementRequiredByOther, bytes) ← decodeUIntLE 1 bytes
  let (reserved200, bytes) ← Alpha.decode 200 bytes
  pure ({ symbolId, mpid, marketMakerNul, mpsubid4, reserved4, clearingNumber, riskUserCrd, riskUserType, riskControlType, usdLimit, timeLimit, percentageLimit, countLimit, breachActionResponse, iocAttribution, usdCalculation1, usdCalculation2, usdCalculation3, usdCalculation4, countCalculation, riskActionType, thresholdBreachLevel, blockedByBreachIndicator, blockedByKillSwitchIndicator, reinstatementRequiredBySelf, reinstatementRequiredByOther, reserved200 }, bytes)

@[simp] theorem encode_length (message : RiskControlAlertMessage) : (encode message).length = 301 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, RiskUserType.encode_length]

theorem encode_length_pos (message : RiskControlAlertMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RiskControlAlertMessage) (rest : List UInt8) :
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
theorem decode_encode_nil (message : RiskControlAlertMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RiskControlAlertMessage

/-- Any Server Sequenced Message, selected by Seq Msg Type -/
inductive ServerSequencedMessage where
  | equitiesSymbolReferenceDataMessage (message : EquitiesSymbolReferenceDataMessage) -- 562
  | dmmSymbolReferenceDataMessage (message : DmmSymbolReferenceDataMessage) -- 2098
  | minimumPriceVariantClassReferenceDataMessage (message : MinimumPriceVariantClassReferenceDataMessage) -- 560
  | minimumPriceVariantLevelReferenceDataMessage (message : MinimumPriceVariantLevelReferenceDataMessage) -- 561
  | mpidConfigurationMessage (message : MpidConfigurationMessage) -- 626
  | mmidConfigurationMessage (message : MmidConfigurationMessage) -- 627
  | sessionConfigurationAcknowledgementMessage (message : SessionConfigurationAcknowledgementMessage) -- 545
  | orderAndCancelReplaceAcknowledgementMessage (message : OrderAndCancelReplaceAcknowledgementMessage) -- 608
  | orderModifyCancelRequestAcknowledgmentAndUroutMessage (message : OrderModifyCancelRequestAcknowledgmentAndUroutMessage) -- 625
  | orderPriorityUpdateAcknowledgmentMessage (message : OrderPriorityUpdateAcknowledgmentMessage) -- 610
  | executionReportMessage (message : ExecutionReportMessage) -- 656
  | tradeBustCorrectMessage (message : TradeBustCorrectMessage) -- 658
  | applicationLayerRejectMessage (message : ApplicationLayerRejectMessage) -- 611
  | symbolSubscriptionAcknowledgementMessage (message : SymbolSubscriptionAcknowledgementMessage) -- 839
  | gtBeginMessage (message : GtBeginMessage) -- 841
  | gtEndMessage (message : GtEndMessage) -- 848
  | auctionPriceDataMessage (message : AuctionPriceDataMessage) -- 850
  | auctionRequestMessage (message : AuctionRequestMessage) -- 840
  | manualActionRequestMessage (message : ManualActionRequestMessage) -- 851
  | riskControlAcknowledgementMessage (message : RiskControlAcknowledgementMessage) -- 818
  | riskControlAlertMessage (message : RiskControlAlertMessage) -- 819
  deriving DecidableEq, Repr

namespace ServerSequencedMessage

/-- The Seq Msg Type each message is sent under -/
def tag : ServerSequencedMessage → BitVec 16
  | .equitiesSymbolReferenceDataMessage _ => 562
  | .dmmSymbolReferenceDataMessage _ => 2098
  | .minimumPriceVariantClassReferenceDataMessage _ => 560
  | .minimumPriceVariantLevelReferenceDataMessage _ => 561
  | .mpidConfigurationMessage _ => 626
  | .mmidConfigurationMessage _ => 627
  | .sessionConfigurationAcknowledgementMessage _ => 545
  | .orderAndCancelReplaceAcknowledgementMessage _ => 608
  | .orderModifyCancelRequestAcknowledgmentAndUroutMessage _ => 625
  | .orderPriorityUpdateAcknowledgmentMessage _ => 610
  | .executionReportMessage _ => 656
  | .tradeBustCorrectMessage _ => 658
  | .applicationLayerRejectMessage _ => 611
  | .symbolSubscriptionAcknowledgementMessage _ => 839
  | .gtBeginMessage _ => 841
  | .gtEndMessage _ => 848
  | .auctionPriceDataMessage _ => 850
  | .auctionRequestMessage _ => 840
  | .manualActionRequestMessage _ => 851
  | .riskControlAcknowledgementMessage _ => 818
  | .riskControlAlertMessage _ => 819

def encode : ServerSequencedMessage → List UInt8
  | .equitiesSymbolReferenceDataMessage message => EquitiesSymbolReferenceDataMessage.encode message
  | .dmmSymbolReferenceDataMessage message => DmmSymbolReferenceDataMessage.encode message
  | .minimumPriceVariantClassReferenceDataMessage message => MinimumPriceVariantClassReferenceDataMessage.encode message
  | .minimumPriceVariantLevelReferenceDataMessage message => MinimumPriceVariantLevelReferenceDataMessage.encode message
  | .mpidConfigurationMessage message => MpidConfigurationMessage.encode message
  | .mmidConfigurationMessage message => MmidConfigurationMessage.encode message
  | .sessionConfigurationAcknowledgementMessage message => SessionConfigurationAcknowledgementMessage.encode message
  | .orderAndCancelReplaceAcknowledgementMessage message => OrderAndCancelReplaceAcknowledgementMessage.encode message
  | .orderModifyCancelRequestAcknowledgmentAndUroutMessage message => OrderModifyCancelRequestAcknowledgmentAndUroutMessage.encode message
  | .orderPriorityUpdateAcknowledgmentMessage message => OrderPriorityUpdateAcknowledgmentMessage.encode message
  | .executionReportMessage message => ExecutionReportMessage.encode message
  | .tradeBustCorrectMessage message => TradeBustCorrectMessage.encode message
  | .applicationLayerRejectMessage message => ApplicationLayerRejectMessage.encode message
  | .symbolSubscriptionAcknowledgementMessage message => SymbolSubscriptionAcknowledgementMessage.encode message
  | .gtBeginMessage message => GtBeginMessage.encode message
  | .gtEndMessage message => GtEndMessage.encode message
  | .auctionPriceDataMessage message => AuctionPriceDataMessage.encode message
  | .auctionRequestMessage message => AuctionRequestMessage.encode message
  | .manualActionRequestMessage message => ManualActionRequestMessage.encode message
  | .riskControlAcknowledgementMessage message => RiskControlAcknowledgementMessage.encode message
  | .riskControlAlertMessage message => RiskControlAlertMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option ServerSequencedMessage :=
  if tag = 562 then (EquitiesSymbolReferenceDataMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.equitiesSymbolReferenceDataMessage message) else none
  else if tag = 2098 then (DmmSymbolReferenceDataMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.dmmSymbolReferenceDataMessage message) else none
  else if tag = 560 then (MinimumPriceVariantClassReferenceDataMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.minimumPriceVariantClassReferenceDataMessage message) else none
  else if tag = 561 then (MinimumPriceVariantLevelReferenceDataMessage.decode bytes).map fun message => .minimumPriceVariantLevelReferenceDataMessage message
  else if tag = 626 then (MpidConfigurationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.mpidConfigurationMessage message) else none
  else if tag = 627 then (MmidConfigurationMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.mmidConfigurationMessage message) else none
  else if tag = 545 then (SessionConfigurationAcknowledgementMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sessionConfigurationAcknowledgementMessage message) else none
  else if tag = 608 then (OrderAndCancelReplaceAcknowledgementMessage.decode bytes).map fun message => .orderAndCancelReplaceAcknowledgementMessage message
  else if tag = 625 then (OrderModifyCancelRequestAcknowledgmentAndUroutMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderModifyCancelRequestAcknowledgmentAndUroutMessage message) else none
  else if tag = 610 then (OrderPriorityUpdateAcknowledgmentMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderPriorityUpdateAcknowledgmentMessage message) else none
  else if tag = 656 then (ExecutionReportMessage.decode bytes).map fun message => .executionReportMessage message
  else if tag = 658 then (TradeBustCorrectMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeBustCorrectMessage message) else none
  else if tag = 611 then (ApplicationLayerRejectMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.applicationLayerRejectMessage message) else none
  else if tag = 839 then (SymbolSubscriptionAcknowledgementMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.symbolSubscriptionAcknowledgementMessage message) else none
  else if tag = 841 then (GtBeginMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.gtBeginMessage message) else none
  else if tag = 848 then (GtEndMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.gtEndMessage message) else none
  else if tag = 850 then (AuctionPriceDataMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.auctionPriceDataMessage message) else none
  else if tag = 840 then (AuctionRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.auctionRequestMessage message) else none
  else if tag = 851 then (ManualActionRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.manualActionRequestMessage message) else none
  else if tag = 818 then (RiskControlAcknowledgementMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.riskControlAcknowledgementMessage message) else none
  else if tag = 819 then (RiskControlAlertMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.riskControlAlertMessage message) else none
  else none

theorem decode_encode (message : ServerSequencedMessage) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | equitiesSymbolReferenceDataMessage message => simp [decode, encode, tag, EquitiesSymbolReferenceDataMessage.decode_encode_nil]
  | dmmSymbolReferenceDataMessage message => simp [decode, encode, tag, DmmSymbolReferenceDataMessage.decode_encode_nil]
  | minimumPriceVariantClassReferenceDataMessage message => simp [decode, encode, tag, MinimumPriceVariantClassReferenceDataMessage.decode_encode_nil]
  | minimumPriceVariantLevelReferenceDataMessage message => simp [decode, encode, tag, MinimumPriceVariantLevelReferenceDataMessage.decode_encode]
  | mpidConfigurationMessage message => simp [decode, encode, tag, MpidConfigurationMessage.decode_encode_nil]
  | mmidConfigurationMessage message => simp [decode, encode, tag, MmidConfigurationMessage.decode_encode_nil]
  | sessionConfigurationAcknowledgementMessage message => simp [decode, encode, tag, SessionConfigurationAcknowledgementMessage.decode_encode_nil]
  | orderAndCancelReplaceAcknowledgementMessage message => simp [decode, encode, tag, OrderAndCancelReplaceAcknowledgementMessage.decode_encode]
  | orderModifyCancelRequestAcknowledgmentAndUroutMessage message => simp [decode, encode, tag, OrderModifyCancelRequestAcknowledgmentAndUroutMessage.decode_encode_nil]
  | orderPriorityUpdateAcknowledgmentMessage message => simp [decode, encode, tag, OrderPriorityUpdateAcknowledgmentMessage.decode_encode_nil]
  | executionReportMessage message => simp [decode, encode, tag, ExecutionReportMessage.decode_encode]
  | tradeBustCorrectMessage message => simp [decode, encode, tag, TradeBustCorrectMessage.decode_encode_nil]
  | applicationLayerRejectMessage message => simp [decode, encode, tag, ApplicationLayerRejectMessage.decode_encode_nil]
  | symbolSubscriptionAcknowledgementMessage message => simp [decode, encode, tag, SymbolSubscriptionAcknowledgementMessage.decode_encode_nil]
  | gtBeginMessage message => simp [decode, encode, tag, GtBeginMessage.decode_encode_nil]
  | gtEndMessage message => simp [decode, encode, tag, GtEndMessage.decode_encode_nil]
  | auctionPriceDataMessage message => simp [decode, encode, tag, AuctionPriceDataMessage.decode_encode_nil]
  | auctionRequestMessage message => simp [decode, encode, tag, AuctionRequestMessage.decode_encode_nil]
  | manualActionRequestMessage message => simp [decode, encode, tag, ManualActionRequestMessage.decode_encode_nil]
  | riskControlAcknowledgementMessage message => simp [decode, encode, tag, RiskControlAcknowledgementMessage.decode_encode_nil]
  | riskControlAlertMessage message => simp [decode, encode, tag, RiskControlAlertMessage.decode_encode_nil]

end ServerSequencedMessage

/-- Server Seq Msg: the body, which the record carries with the proof it fits its frame -/
structure ServerSeqMsgBody where
  seqMsgId : SeqMsgId
  reserved4 : Alpha 4
  timestamp : BitVec 64
  seqMsgLength : BitVec 16
  serverSequencedMessage : ServerSequencedMessage
  deriving DecidableEq, Repr

namespace ServerSeqMsgBody

def encodeBody (message : ServerSeqMsgBody) : List UInt8 :=
  SeqMsgId.encode message.seqMsgId
    ++ (Alpha.encode message.reserved4
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 (ServerSequencedMessage.tag message.serverSequencedMessage)
    ++ (encodeUIntLE 2 message.seqMsgLength
    ++ (ServerSequencedMessage.encode message.serverSequencedMessage)))))

def decodeBody (bytes : List UInt8) : Option ServerSeqMsgBody := do
  let (seqMsgId, bytes) ← SeqMsgId.decode bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (seqMsgType, bytes) ← decodeUIntLE 2 bytes
  let (seqMsgLength, bytes) ← decodeUIntLE 2 bytes
  let serverSequencedMessage ← ServerSequencedMessage.decode seqMsgType bytes
  pure { seqMsgId, reserved4, timestamp, seqMsgLength, serverSequencedMessage }

theorem decodeBody_encodeBody (message : ServerSeqMsgBody) : decodeBody (encodeBody message) = some message := by
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
  rw [ServerSequencedMessage.decode_encode, some_bind]
  rfl

end ServerSeqMsgBody

/-- Server Seq Msg: the body with the proof its encoding fits Msg Length, whose 2 bytes no bound of the fields fits -/
abbrev ServerSeqMsg := Fitting ServerSeqMsgBody.encodeBody 4 65536

namespace ServerSeqMsg

def encode (message : ServerSeqMsg) : List UInt8 :=
  encodeFramedLE 2 4 ServerSeqMsgBody.encodeBody message.val

def decode : List UInt8 → Option (ServerSeqMsg × List UInt8) :=
  decodeFittingAllLE 2 4 ServerSeqMsgBody.encodeBody ServerSeqMsgBody.decodeBody

@[simp] theorem decode_encode (message : ServerSeqMsg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAllLE_encodeFramedLE 2 4 ServerSeqMsgBody.encodeBody ServerSeqMsgBody.decodeBody message (ServerSeqMsgBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : ServerSeqMsg) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : ServerSeqMsg) : (encode message).length ≤ 65533 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramedLE_length]
  omega

end ServerSeqMsg

/-- Any Server Message, selected by Msg Type -/
inductive ServerMessage where
  | loginResponse (message : LoginResponse) -- 514
  | streamAvail (message : StreamAvail) -- 515
  | heartbeat (message : Heartbeat) -- 516
  | openResponse (message : OpenResponse) -- 518
  | closeResponse (message : CloseResponse) -- 520
  | serverSeqMsg (message : ServerSeqMsg) -- 2309
  deriving DecidableEq, Repr

namespace ServerMessage

/-- The Msg Type each message is sent under -/
def tag : ServerMessage → BitVec 16
  | .loginResponse _ => 514
  | .streamAvail _ => 515
  | .heartbeat _ => 516
  | .openResponse _ => 518
  | .closeResponse _ => 520
  | .serverSeqMsg _ => 2309

def encode : ServerMessage → List UInt8
  | .loginResponse message => LoginResponse.encode message
  | .streamAvail message => StreamAvail.encode message
  | .heartbeat message => Heartbeat.encode message
  | .openResponse message => OpenResponse.encode message
  | .closeResponse message => CloseResponse.encode message
  | .serverSeqMsg message => ServerSeqMsg.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerMessage × List UInt8) :=
  if tag = 514 then (LoginResponse.decode bytes).map fun (message, rest) => (.loginResponse message, rest)
  else if tag = 515 then (StreamAvail.decode bytes).map fun (message, rest) => (.streamAvail message, rest)
  else if tag = 516 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 518 then (OpenResponse.decode bytes).map fun (message, rest) => (.openResponse message, rest)
  else if tag = 520 then (CloseResponse.decode bytes).map fun (message, rest) => (.closeResponse message, rest)
  else if tag = 2309 then (ServerSeqMsg.decode bytes).map fun (message, rest) => (.serverSeqMsg message, rest)
  else none

@[simp] theorem decode_encode (message : ServerMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerMessage

/-- Server Pillar Message -/
structure ServerPillarMessage where
  serverMessage : ServerMessage
  deriving DecidableEq, Repr

namespace ServerPillarMessage

def encode (message : ServerPillarMessage) : List UInt8 :=
  encodeUIntLE 2 (ServerMessage.tag message.serverMessage)
    ++ (ServerMessage.encode message.serverMessage)

def decode (bytes : List UInt8) : Option (ServerPillarMessage × List UInt8) := do
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (serverMessage, bytes) ← ServerMessage.decode msgType bytes
  pure ({ serverMessage }, bytes)

theorem encode_length_pos (message : ServerPillarMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : ServerPillarMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ServerMessage.decode_encode, some_bind]
  rfl

end ServerPillarMessage

end Omi.NyseNationalequitiesBinarygatewayPillarstreamV60ServerPillarMessage
