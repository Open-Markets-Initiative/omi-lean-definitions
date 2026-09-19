import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Orders v5.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Appendage Length and the Account Query Appendage it sizes are there only when bytes remain after Account Query Message's fixed fields: they are read as one optional closing field.

Note: Unsequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Note: Client Soup Bin Tcp Packet's body has no bound its 2 byte Packet Length must fit, so every message carries the proof its own encoding fits: the record is its body with that proof, checked as the frame is read.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesOrdersOuchV50Client

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x54, 0x45]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .sellShort => 0x54
  | .sellShortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x54 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | sellShort => decide
  | sellShortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Time In Force: one byte code -/
def TimeInForce.codes : List UInt8 :=
  [0x30, 0x33, 0x35, 0x36, 0x45]

inductive TimeInForce where
  | day -- Day
  | ioc -- Ioc
  | gtxExtendedHours -- Gtx Extended Hours
  | gtt -- Gtt
  | afterHours -- After Hours
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .day => 0x30
  | .ioc => 0x33
  | .gtxExtendedHours => 0x35
  | .gtt => 0x36
  | .afterHours => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x30 then .day
  else if byte = 0x33 then .ioc
  else if byte = 0x35 then .gtxExtendedHours
  else if byte = 0x36 then .gtt
  else .afterHours

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | ioc => decide
  | gtxExtendedHours => decide
  | gtt => decide
  | afterHours => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForce) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForce × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForce) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TimeInForce) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForce

/-- Display: one byte code -/
def Display.codes : List UInt8 :=
  [0x41, 0x59, 0x4E, 0x50, 0x49, 0x4D, 0x57, 0x4C, 0x4F, 0x54, 0x51, 0x5A, 0x6D, 0x6E]

inductive Display where
  | attributable -- Attributable
  | visible -- Visible
  | hidden -- Hidden
  | postOnly -- Post Only
  | imbalanceOnly -- Imbalance Only
  | midPointPeg -- Mid Point Peg
  | midPointPegPostOnly -- Mid Point Peg Post Only
  | postOnlyAndAttributable -- Post Only And Attributable
  | retailOrderType1 -- Retail Order Type 1
  | retailOrderType2 -- Retail Order Type 2
  | retailPriceImprovementOrder -- Retail Price Improvement Order
  | conformant -- Conformant
  | midPointPegAndMidPointTradeNow -- Mid Point Peg And Mid Point Trade Now
  | nonDisplayAndMidPoint -- Non Display And Mid Point
  | unlisted (byte : { byte : UInt8 // byte ∉ Display.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Display

def toByte : Display → UInt8
  | .attributable => 0x41
  | .visible => 0x59
  | .hidden => 0x4E
  | .postOnly => 0x50
  | .imbalanceOnly => 0x49
  | .midPointPeg => 0x4D
  | .midPointPegPostOnly => 0x57
  | .postOnlyAndAttributable => 0x4C
  | .retailOrderType1 => 0x4F
  | .retailOrderType2 => 0x54
  | .retailPriceImprovementOrder => 0x51
  | .conformant => 0x5A
  | .midPointPegAndMidPointTradeNow => 0x6D
  | .nonDisplayAndMidPoint => 0x6E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Display :=
  if byte = 0x41 then .attributable
  else if byte = 0x59 then .visible
  else if byte = 0x4E then .hidden
  else if byte = 0x50 then .postOnly
  else if byte = 0x49 then .imbalanceOnly
  else if byte = 0x4D then .midPointPeg
  else if byte = 0x57 then .midPointPegPostOnly
  else if byte = 0x4C then .postOnlyAndAttributable
  else if byte = 0x4F then .retailOrderType1
  else if byte = 0x54 then .retailOrderType2
  else if byte = 0x51 then .retailPriceImprovementOrder
  else if byte = 0x5A then .conformant
  else if byte = 0x6D then .midPointPegAndMidPointTradeNow
  else .nonDisplayAndMidPoint

def ofByte (byte : UInt8) : Display :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Display) : ofByte value.toByte = value := by
  cases value with
  | attributable => decide
  | visible => decide
  | hidden => decide
  | postOnly => decide
  | imbalanceOnly => decide
  | midPointPeg => decide
  | midPointPegPostOnly => decide
  | postOnlyAndAttributable => decide
  | retailOrderType1 => decide
  | retailOrderType2 => decide
  | retailPriceImprovementOrder => decide
  | conformant => decide
  | midPointPegAndMidPointTradeNow => decide
  | nonDisplayAndMidPoint => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Display) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Display × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Display) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Display) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Display

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x4F, 0x41, 0x50, 0x52]

inductive Capacity where
  | other -- Other
  | agency -- Agency
  | principal -- Principal
  | riskless -- Riskless
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .other => 0x4F
  | .agency => 0x41
  | .principal => 0x50
  | .riskless => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x4F then .other
  else if byte = 0x41 then .agency
  else if byte = 0x50 then .principal
  else .riskless

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | other => decide
  | agency => decide
  | principal => decide
  | riskless => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Capacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Capacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Capacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Capacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Capacity

/-- Inter Market Sweep Eligibility: one byte code -/
def InterMarketSweepEligibility.codes : List UInt8 :=
  [0x59, 0x4E]

inductive InterMarketSweepEligibility where
  | eligible -- Eligible
  | notEligible -- Not Eligible
  | unlisted (byte : { byte : UInt8 // byte ∉ InterMarketSweepEligibility.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InterMarketSweepEligibility

def toByte : InterMarketSweepEligibility → UInt8
  | .eligible => 0x59
  | .notEligible => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InterMarketSweepEligibility :=
  if byte = 0x59 then .eligible
  else .notEligible

def ofByte (byte : UInt8) : InterMarketSweepEligibility :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InterMarketSweepEligibility) : ofByte value.toByte = value := by
  cases value with
  | eligible => decide
  | notEligible => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InterMarketSweepEligibility) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InterMarketSweepEligibility × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InterMarketSweepEligibility) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InterMarketSweepEligibility) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InterMarketSweepEligibility

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4E, 0x4F, 0x43, 0x48, 0x53, 0x52, 0x45, 0x41]

inductive CrossType where
  | continuousMarket -- Continuous Market
  | openingCross -- Opening Cross
  | closing -- Closing
  | haltIpo -- Halt Ipo
  | supplemental -- Supplemental
  | retail -- Retail
  | extended -- Extended
  | afterHoursClose -- After Hours Close
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .continuousMarket => 0x4E
  | .openingCross => 0x4F
  | .closing => 0x43
  | .haltIpo => 0x48
  | .supplemental => 0x53
  | .retail => 0x52
  | .extended => 0x45
  | .afterHoursClose => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4E then .continuousMarket
  else if byte = 0x4F then .openingCross
  else if byte = 0x43 then .closing
  else if byte = 0x48 then .haltIpo
  else if byte = 0x53 then .supplemental
  else if byte = 0x52 then .retail
  else if byte = 0x45 then .extended
  else .afterHoursClose

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | continuousMarket => decide
  | openingCross => decide
  | closing => decide
  | haltIpo => decide
  | supplemental => decide
  | retail => decide
  | extended => decide
  | afterHoursClose => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CrossType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossType

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  text : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (text, bytes) ← Alpha.decode 1 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : DebugPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DebugPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebugPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DebugPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DebugPacket

/-- Login Request Packet: 46 bytes -/
structure LoginRequestPacket where
  username : Alpha 6
  password : Alpha 10
  requestedSession : Alpha 10
  requestedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginRequestPacket

def encode (message : LoginRequestPacket) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.requestedSession
    ++ (Alpha.encode message.requestedSequenceNumber)))

def decode (bytes : List UInt8) : Option (LoginRequestPacket × List UInt8) := do
  let (username, bytes) ← Alpha.decode 6 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (requestedSession, bytes) ← Alpha.decode 10 bytes
  let (requestedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ username, password, requestedSession, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequestPacket) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequestPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequestPacket

/-- Firm: 4 bytes -/
structure FirmValue where
  firm : Alpha 4
  deriving DecidableEq, Repr

namespace FirmValue

def encode (message : FirmValue) : List UInt8 :=
  Alpha.encode message.firm

def decode (bytes : List UInt8) : Option (FirmValue × List UInt8) := do
  let (firm, bytes) ← Alpha.decode 4 bytes
  pure ({ firm }, bytes)

@[simp] theorem encode_length (message : FirmValue) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : FirmValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FirmValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end FirmValue

/-- Min Qty: 4 bytes -/
structure MinQtyValue where
  minQty : BitVec 32
  deriving DecidableEq, Repr

namespace MinQtyValue

def encode (message : MinQtyValue) : List UInt8 :=
  encodeUInt 4 message.minQty

def decode (bytes : List UInt8) : Option (MinQtyValue × List UInt8) := do
  let (minQty, bytes) ← decodeUInt 4 bytes
  pure ({ minQty }, bytes)

@[simp] theorem encode_length (message : MinQtyValue) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MinQtyValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinQtyValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinQtyValue

/-- Customer Type: 1 bytes -/
structure CustomerTypeValue where
  customerType : Alpha 1
  deriving DecidableEq, Repr

namespace CustomerTypeValue

def encode (message : CustomerTypeValue) : List UInt8 :=
  Alpha.encode message.customerType

def decode (bytes : List UInt8) : Option (CustomerTypeValue × List UInt8) := do
  let (customerType, bytes) ← Alpha.decode 1 bytes
  pure ({ customerType }, bytes)

@[simp] theorem encode_length (message : CustomerTypeValue) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CustomerTypeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CustomerTypeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end CustomerTypeValue

/-- Max Floor: 4 bytes -/
structure MaxFloorValue where
  maxFloor : BitVec 32
  deriving DecidableEq, Repr

namespace MaxFloorValue

def encode (message : MaxFloorValue) : List UInt8 :=
  encodeUInt 4 message.maxFloor

def decode (bytes : List UInt8) : Option (MaxFloorValue × List UInt8) := do
  let (maxFloor, bytes) ← decodeUInt 4 bytes
  pure ({ maxFloor }, bytes)

@[simp] theorem encode_length (message : MaxFloorValue) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MaxFloorValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaxFloorValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaxFloorValue

/-- Any Enter Order Optional Value, selected by Enter Order Optional Field -/
inductive EnterOrderOptionalValue where
  | firm (message : FirmValue) -- 2
  | minQty (message : MinQtyValue) -- 3
  | customerType (message : CustomerTypeValue) -- 4
  | maxFloor (message : MaxFloorValue) -- 5
  deriving DecidableEq, Repr

namespace EnterOrderOptionalValue

/-- The Enter Order Optional Field each message is sent under -/
def tag : EnterOrderOptionalValue → BitVec 8
  | .firm _ => 2
  | .minQty _ => 3
  | .customerType _ => 4
  | .maxFloor _ => 5

def encode : EnterOrderOptionalValue → List UInt8
  | .firm message => FirmValue.encode message
  | .minQty message => MinQtyValue.encode message
  | .customerType message => CustomerTypeValue.encode message
  | .maxFloor message => MaxFloorValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : EnterOrderOptionalValue) : (encode message).length ≤ 4 := by
  cases message with
  | firm inner =>
    simp only [encode, FirmValue.encode_length]
    omega
  | minQty inner =>
    simp only [encode, MinQtyValue.encode_length]
    omega
  | customerType inner =>
    simp only [encode, CustomerTypeValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [encode, MaxFloorValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (EnterOrderOptionalValue × List UInt8) :=
  if tag = 2 then (FirmValue.decode bytes).map fun (message, rest) => (.firm message, rest)
  else if tag = 3 then (MinQtyValue.decode bytes).map fun (message, rest) => (.minQty message, rest)
  else if tag = 4 then (CustomerTypeValue.decode bytes).map fun (message, rest) => (.customerType message, rest)
  else if tag = 5 then (MaxFloorValue.decode bytes).map fun (message, rest) => (.maxFloor message, rest)
  else none

@[simp] theorem decode_encode (message : EnterOrderOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end EnterOrderOptionalValue

/-- Enter Order Appendage -/
structure EnterOrderAppendage where
  enterOrderOptionalValue : EnterOrderOptionalValue
  deriving DecidableEq, Repr

namespace EnterOrderAppendage

def encodeBody (message : EnterOrderAppendage) : List UInt8 :=
  encodeUInt 1 (EnterOrderOptionalValue.tag message.enterOrderOptionalValue)
    ++ (EnterOrderOptionalValue.encode message.enterOrderOptionalValue)

def decodeBody (bytes : List UInt8) : Option (EnterOrderAppendage × List UInt8) := do
  let (enterOrderOptionalField, bytes) ← decodeUInt 1 bytes
  let (enterOrderOptionalValue, bytes) ← EnterOrderOptionalValue.decode enterOrderOptionalField bytes
  pure ({ enterOrderOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : EnterOrderAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EnterOrderOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : EnterOrderAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.enterOrderOptionalValue with
  | firm inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, FirmValue.encode_length]
    omega
  | minQty inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, MinQtyValue.encode_length]
    omega
  | customerType inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, CustomerTypeValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [EnterOrderOptionalValue.encode, List.length_append, encodeUInt_length, MaxFloorValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : EnterOrderAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (EnterOrderAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : EnterOrderAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : EnterOrderAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end EnterOrderAppendage

/-- Enter Order Message -/
structure EnterOrderMessage where
  userRefNum : BitVec 32
  side : Side
  quantity : BitVec 32
  symbol : Alpha 8
  price : BitVec 64
  timeInForce : TimeInForce
  display : Display
  capacity : Capacity
  interMarketSweepEligibility : InterMarketSweepEligibility
  crossType : CrossType
  clordid : Alpha 14
  enterOrderAppendage : Sized 2 EnterOrderAppendage.encode
  deriving DecidableEq, Repr

namespace EnterOrderMessage

def encode (message : EnterOrderMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.quantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.price
    ++ (TimeInForce.encode message.timeInForce
    ++ (Display.encode message.display
    ++ (Capacity.encode message.capacity
    ++ (InterMarketSweepEligibility.encode message.interMarketSweepEligibility
    ++ (CrossType.encode message.crossType
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany EnterOrderAppendage.encode message.enterOrderAppendage.val).length)
    ++ (encodeMany EnterOrderAppendage.encode message.enterOrderAppendage.val))))))))))))

def decode (bytes : List UInt8) : Option (EnterOrderMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (display, bytes) ← Display.decode bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (interMarketSweepEligibility, bytes) ← InterMarketSweepEligibility.decode bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (clordid, bytes) ← Alpha.decode 14 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (enterOrderAppendage_, bytes) ← decodeSized EnterOrderAppendage.decode appendageLength.toNat bytes
  if fits_enterOrderAppendage : (encodeMany EnterOrderAppendage.encode enterOrderAppendage_).length < 256 ^ 2 then
    pure ({ userRefNum, side, quantity, symbol, price, timeInForce, display, capacity, interMarketSweepEligibility, crossType, clordid, enterOrderAppendage := ⟨enterOrderAppendage_, fits_enterOrderAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : EnterOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EnterOrderMessage) : (encode message).length ≤ 65581 := by
  have bound_enterOrderAppendage := message.enterOrderAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Side.encode_length, Alpha.encode_length, TimeInForce.encode_length, Display.encode_length, Capacity.encode_length, InterMarketSweepEligibility.encode_length, CrossType.encode_length]
  omega

@[simp] theorem decode_encode (message : EnterOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InterMarketSweepEligibility.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 EnterOrderAppendage.encode EnterOrderAppendage.decode EnterOrderAppendage.decode_encode EnterOrderAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.enterOrderAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EnterOrderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EnterOrderMessage

/-- Price Type: 1 bytes -/
structure PriceTypeValue where
  priceType : Alpha 1
  deriving DecidableEq, Repr

namespace PriceTypeValue

def encode (message : PriceTypeValue) : List UInt8 :=
  Alpha.encode message.priceType

def decode (bytes : List UInt8) : Option (PriceTypeValue × List UInt8) := do
  let (priceType, bytes) ← Alpha.decode 1 bytes
  pure ({ priceType }, bytes)

@[simp] theorem encode_length (message : PriceTypeValue) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : PriceTypeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceTypeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end PriceTypeValue

/-- Post Only: 1 bytes -/
structure PostOnlyValue where
  postOnly : Alpha 1
  deriving DecidableEq, Repr

namespace PostOnlyValue

def encode (message : PostOnlyValue) : List UInt8 :=
  Alpha.encode message.postOnly

def decode (bytes : List UInt8) : Option (PostOnlyValue × List UInt8) := do
  let (postOnly, bytes) ← Alpha.decode 1 bytes
  pure ({ postOnly }, bytes)

@[simp] theorem encode_length (message : PostOnlyValue) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : PostOnlyValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PostOnlyValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end PostOnlyValue

/-- Expire Time: 4 bytes -/
structure ExpireTimeValue where
  expireTime : BitVec 32
  deriving DecidableEq, Repr

namespace ExpireTimeValue

def encode (message : ExpireTimeValue) : List UInt8 :=
  encodeUInt 4 message.expireTime

def decode (bytes : List UInt8) : Option (ExpireTimeValue × List UInt8) := do
  let (expireTime, bytes) ← decodeUInt 4 bytes
  pure ({ expireTime }, bytes)

@[simp] theorem encode_length (message : ExpireTimeValue) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ExpireTimeValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExpireTimeValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExpireTimeValue

/-- Trade Now: 1 bytes -/
structure TradeNowValue where
  tradeNow : Alpha 1
  deriving DecidableEq, Repr

namespace TradeNowValue

def encode (message : TradeNowValue) : List UInt8 :=
  Alpha.encode message.tradeNow

def decode (bytes : List UInt8) : Option (TradeNowValue × List UInt8) := do
  let (tradeNow, bytes) ← Alpha.decode 1 bytes
  pure ({ tradeNow }, bytes)

@[simp] theorem encode_length (message : TradeNowValue) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : TradeNowValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeNowValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeNowValue

/-- Handle Inst: 1 bytes -/
structure HandleInstValue where
  handleInst : Alpha 1
  deriving DecidableEq, Repr

namespace HandleInstValue

def encode (message : HandleInstValue) : List UInt8 :=
  Alpha.encode message.handleInst

def decode (bytes : List UInt8) : Option (HandleInstValue × List UInt8) := do
  let (handleInst, bytes) ← Alpha.decode 1 bytes
  pure ({ handleInst }, bytes)

@[simp] theorem encode_length (message : HandleInstValue) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : HandleInstValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HandleInstValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end HandleInstValue

/-- Any Replace Order Optional Value, selected by Replace Order Optional Field -/
inductive ReplaceOrderOptionalValue where
  | minQty (message : MinQtyValue) -- 3
  | maxFloor (message : MaxFloorValue) -- 5
  | priceType (message : PriceTypeValue) -- 6
  | postOnly (message : PostOnlyValue) -- 12
  | expireTime (message : ExpireTimeValue) -- 15
  | tradeNow (message : TradeNowValue) -- 16
  | handleInst (message : HandleInstValue) -- 17
  deriving DecidableEq, Repr

namespace ReplaceOrderOptionalValue

/-- The Replace Order Optional Field each message is sent under -/
def tag : ReplaceOrderOptionalValue → BitVec 8
  | .minQty _ => 3
  | .maxFloor _ => 5
  | .priceType _ => 6
  | .postOnly _ => 12
  | .expireTime _ => 15
  | .tradeNow _ => 16
  | .handleInst _ => 17

def encode : ReplaceOrderOptionalValue → List UInt8
  | .minQty message => MinQtyValue.encode message
  | .maxFloor message => MaxFloorValue.encode message
  | .priceType message => PriceTypeValue.encode message
  | .postOnly message => PostOnlyValue.encode message
  | .expireTime message => ExpireTimeValue.encode message
  | .tradeNow message => TradeNowValue.encode message
  | .handleInst message => HandleInstValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ReplaceOrderOptionalValue) : (encode message).length ≤ 4 := by
  cases message with
  | minQty inner =>
    simp only [encode, MinQtyValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [encode, MaxFloorValue.encode_length]
    omega
  | priceType inner =>
    simp only [encode, PriceTypeValue.encode_length]
    omega
  | postOnly inner =>
    simp only [encode, PostOnlyValue.encode_length]
    omega
  | expireTime inner =>
    simp only [encode, ExpireTimeValue.encode_length]
    omega
  | tradeNow inner =>
    simp only [encode, TradeNowValue.encode_length]
    omega
  | handleInst inner =>
    simp only [encode, HandleInstValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ReplaceOrderOptionalValue × List UInt8) :=
  if tag = 3 then (MinQtyValue.decode bytes).map fun (message, rest) => (.minQty message, rest)
  else if tag = 5 then (MaxFloorValue.decode bytes).map fun (message, rest) => (.maxFloor message, rest)
  else if tag = 6 then (PriceTypeValue.decode bytes).map fun (message, rest) => (.priceType message, rest)
  else if tag = 12 then (PostOnlyValue.decode bytes).map fun (message, rest) => (.postOnly message, rest)
  else if tag = 15 then (ExpireTimeValue.decode bytes).map fun (message, rest) => (.expireTime message, rest)
  else if tag = 16 then (TradeNowValue.decode bytes).map fun (message, rest) => (.tradeNow message, rest)
  else if tag = 17 then (HandleInstValue.decode bytes).map fun (message, rest) => (.handleInst message, rest)
  else none

@[simp] theorem decode_encode (message : ReplaceOrderOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ReplaceOrderOptionalValue

/-- Replace Order Appendage -/
structure ReplaceOrderAppendage where
  replaceOrderOptionalValue : ReplaceOrderOptionalValue
  deriving DecidableEq, Repr

namespace ReplaceOrderAppendage

def encodeBody (message : ReplaceOrderAppendage) : List UInt8 :=
  encodeUInt 1 (ReplaceOrderOptionalValue.tag message.replaceOrderOptionalValue)
    ++ (ReplaceOrderOptionalValue.encode message.replaceOrderOptionalValue)

def decodeBody (bytes : List UInt8) : Option (ReplaceOrderAppendage × List UInt8) := do
  let (replaceOrderOptionalField, bytes) ← decodeUInt 1 bytes
  let (replaceOrderOptionalValue, bytes) ← ReplaceOrderOptionalValue.decode replaceOrderOptionalField bytes
  pure ({ replaceOrderOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : ReplaceOrderAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ReplaceOrderOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ReplaceOrderAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.replaceOrderOptionalValue with
  | minQty inner =>
    simp only [ReplaceOrderOptionalValue.encode, List.length_append, encodeUInt_length, MinQtyValue.encode_length]
    omega
  | maxFloor inner =>
    simp only [ReplaceOrderOptionalValue.encode, List.length_append, encodeUInt_length, MaxFloorValue.encode_length]
    omega
  | priceType inner =>
    simp only [ReplaceOrderOptionalValue.encode, List.length_append, encodeUInt_length, PriceTypeValue.encode_length]
    omega
  | postOnly inner =>
    simp only [ReplaceOrderOptionalValue.encode, List.length_append, encodeUInt_length, PostOnlyValue.encode_length]
    omega
  | expireTime inner =>
    simp only [ReplaceOrderOptionalValue.encode, List.length_append, encodeUInt_length, ExpireTimeValue.encode_length]
    omega
  | tradeNow inner =>
    simp only [ReplaceOrderOptionalValue.encode, List.length_append, encodeUInt_length, TradeNowValue.encode_length]
    omega
  | handleInst inner =>
    simp only [ReplaceOrderOptionalValue.encode, List.length_append, encodeUInt_length, HandleInstValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ReplaceOrderAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (ReplaceOrderAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : ReplaceOrderAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ReplaceOrderAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ReplaceOrderAppendage

/-- Replace Order Message -/
structure ReplaceOrderMessage where
  origUserRefNum : BitVec 32
  userRefNum : BitVec 32
  quantity : BitVec 32
  price : BitVec 64
  timeInForce : TimeInForce
  display : Display
  interMarketSweepEligibility : InterMarketSweepEligibility
  clordid : Alpha 14
  replaceOrderAppendage : Sized 2 ReplaceOrderAppendage.encode
  deriving DecidableEq, Repr

namespace ReplaceOrderMessage

def encode (message : ReplaceOrderMessage) : List UInt8 :=
  encodeUInt 4 message.origUserRefNum
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price
    ++ (TimeInForce.encode message.timeInForce
    ++ (Display.encode message.display
    ++ (InterMarketSweepEligibility.encode message.interMarketSweepEligibility
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany ReplaceOrderAppendage.encode message.replaceOrderAppendage.val).length)
    ++ (encodeMany ReplaceOrderAppendage.encode message.replaceOrderAppendage.val)))))))))

def decode (bytes : List UInt8) : Option (ReplaceOrderMessage × List UInt8) := do
  let (origUserRefNum, bytes) ← decodeUInt 4 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (display, bytes) ← Display.decode bytes
  let (interMarketSweepEligibility, bytes) ← InterMarketSweepEligibility.decode bytes
  let (clordid, bytes) ← Alpha.decode 14 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (replaceOrderAppendage_, bytes) ← decodeSized ReplaceOrderAppendage.decode appendageLength.toNat bytes
  if fits_replaceOrderAppendage : (encodeMany ReplaceOrderAppendage.encode replaceOrderAppendage_).length < 256 ^ 2 then
    pure ({ origUserRefNum, userRefNum, quantity, price, timeInForce, display, interMarketSweepEligibility, clordid, replaceOrderAppendage := ⟨replaceOrderAppendage_, fits_replaceOrderAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : ReplaceOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReplaceOrderMessage) : (encode message).length ≤ 65574 := by
  have bound_replaceOrderAppendage := message.replaceOrderAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, TimeInForce.encode_length, Display.encode_length, InterMarketSweepEligibility.encode_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : ReplaceOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InterMarketSweepEligibility.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 ReplaceOrderAppendage.encode ReplaceOrderAppendage.decode ReplaceOrderAppendage.decode_encode ReplaceOrderAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.replaceOrderAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ReplaceOrderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ReplaceOrderMessage

/-- Cancel Order Message: 8 bytes -/
structure CancelOrderMessage where
  userRefNum : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace CancelOrderMessage

def encode (message : CancelOrderMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.quantity)

def decode (bytes : List UInt8) : Option (CancelOrderMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ userRefNum, quantity }, bytes)

@[simp] theorem encode_length (message : CancelOrderMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : CancelOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : CancelOrderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end CancelOrderMessage

/-- Modify Order Message: 9 bytes -/
structure ModifyOrderMessage where
  userRefNum : BitVec 32
  side : Side
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace ModifyOrderMessage

def encode (message : ModifyOrderMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.quantity))

def decode (bytes : List UInt8) : Option (ModifyOrderMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ userRefNum, side, quantity }, bytes)

@[simp] theorem encode_length (message : ModifyOrderMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : ModifyOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ModifyOrderMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ModifyOrderMessage

/-- User Ref Idx: 1 bytes -/
structure UserRefIdxValue where
  userRefIdx : BitVec 8
  deriving DecidableEq, Repr

namespace UserRefIdxValue

def encode (message : UserRefIdxValue) : List UInt8 :=
  encodeUInt 1 message.userRefIdx

def decode (bytes : List UInt8) : Option (UserRefIdxValue × List UInt8) := do
  let (userRefIdx, bytes) ← decodeUInt 1 bytes
  pure ({ userRefIdx }, bytes)

@[simp] theorem encode_length (message : UserRefIdxValue) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : UserRefIdxValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserRefIdxValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end UserRefIdxValue

/-- Any Account Query Optional Value, selected by Account Query Optional Field -/
inductive AccountQueryOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace AccountQueryOptionalValue

/-- The Account Query Optional Field each message is sent under -/
def tag : AccountQueryOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : AccountQueryOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : AccountQueryOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (AccountQueryOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : AccountQueryOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end AccountQueryOptionalValue

/-- Account Query Appendage -/
structure AccountQueryAppendage where
  accountQueryOptionalValue : AccountQueryOptionalValue
  deriving DecidableEq, Repr

namespace AccountQueryAppendage

def encodeBody (message : AccountQueryAppendage) : List UInt8 :=
  encodeUInt 1 (AccountQueryOptionalValue.tag message.accountQueryOptionalValue)
    ++ (AccountQueryOptionalValue.encode message.accountQueryOptionalValue)

def decodeBody (bytes : List UInt8) : Option (AccountQueryAppendage × List UInt8) := do
  let (accountQueryOptionalField, bytes) ← decodeUInt 1 bytes
  let (accountQueryOptionalValue, bytes) ← AccountQueryOptionalValue.decode accountQueryOptionalField bytes
  pure ({ accountQueryOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : AccountQueryAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [AccountQueryOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : AccountQueryAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.accountQueryOptionalValue with
  | userRefIdx inner =>
    simp only [AccountQueryOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : AccountQueryAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (AccountQueryAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : AccountQueryAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : AccountQueryAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end AccountQueryAppendage

/-- Account Query Message -/
structure AccountQueryMessage where
  accountQueryAppendage : Option (Sized 2 AccountQueryAppendage.encode)
  deriving DecidableEq, Repr

namespace AccountQueryMessage

/-- The Account Query Appendage when there: its length, then the entries filling it -/
def encodeAccountQueryAppendage (items : Sized 2 AccountQueryAppendage.encode) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany AccountQueryAppendage.encode items.val).length) ++ encodeMany AccountQueryAppendage.encode items.val

def decodeAccountQueryAppendage (bytes : List UInt8) : Option (Sized 2 AccountQueryAppendage.encode × List UInt8) := do
  let (length, bytes) ← decodeUInt 2 bytes
  let (items_, bytes) ← decodeSized AccountQueryAppendage.decode length.toNat bytes
  if fits : (encodeMany AccountQueryAppendage.encode items_).length < 256 ^ 2 then pure (⟨items_, fits⟩, bytes) else none

theorem decodeAccountQueryAppendage_encodeAccountQueryAppendage (items : Sized 2 AccountQueryAppendage.encode) (rest : List UInt8) :
    decodeAccountQueryAppendage (encodeAccountQueryAppendage items ++ rest) = some (items, rest) := by
  unfold decodeAccountQueryAppendage encodeAccountQueryAppendage
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 AccountQueryAppendage.encode AccountQueryAppendage.decode AccountQueryAppendage.decode_encode AccountQueryAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left items.length_lt]
  rfl

theorem encodeAccountQueryAppendage_length_pos (items : Sized 2 AccountQueryAppendage.encode) : (encodeAccountQueryAppendage items).length > 0 := by
  unfold encodeAccountQueryAppendage
  simp only [List.length_append, encodeUInt_length]
  omega

def encode (message : AccountQueryMessage) : List UInt8 :=
  encodeTail encodeAccountQueryAppendage message.accountQueryAppendage

def decode (bytes : List UInt8) : Option AccountQueryMessage := do
  let accountQueryAppendage ← decodeTail decodeAccountQueryAppendage bytes
  pure { accountQueryAppendage }

theorem decode_encode (message : AccountQueryMessage) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeTail_encodeTail encodeAccountQueryAppendage decodeAccountQueryAppendage decodeAccountQueryAppendage_encodeAccountQueryAppendage encodeAccountQueryAppendage_length_pos, some_bind]
  rfl

end AccountQueryMessage

/-- Side: 1 bytes -/
structure SideValue where
  side : Side
  deriving DecidableEq, Repr

namespace SideValue

def encode (message : SideValue) : List UInt8 :=
  Side.encode message.side

def decode (bytes : List UInt8) : Option (SideValue × List UInt8) := do
  let (side, bytes) ← Side.decode bytes
  pure ({ side }, bytes)

@[simp] theorem encode_length (message : SideValue) : (encode message).length = 1 := by
  unfold encode
  simp only [Side.encode_length]

theorem encode_length_pos (message : SideValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SideValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Side.decode_encode, some_bind]
  rfl

end SideValue

/-- Group Id: 2 bytes -/
structure GroupIdValue where
  groupId : BitVec 16
  deriving DecidableEq, Repr

namespace GroupIdValue

def encode (message : GroupIdValue) : List UInt8 :=
  encodeUInt 2 message.groupId

def decode (bytes : List UInt8) : Option (GroupIdValue × List UInt8) := do
  let (groupId, bytes) ← decodeUInt 2 bytes
  pure ({ groupId }, bytes)

@[simp] theorem encode_length (message : GroupIdValue) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : GroupIdValue) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupIdValue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end GroupIdValue

/-- Any Mass Cancel Request Optional Value, selected by Mass Cancel Request Optional Field -/
inductive MassCancelRequestOptionalValue where
  | side (message : SideValue) -- 27
  | groupId (message : GroupIdValue) -- 24
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace MassCancelRequestOptionalValue

/-- The Mass Cancel Request Optional Field each message is sent under -/
def tag : MassCancelRequestOptionalValue → BitVec 8
  | .side _ => 27
  | .groupId _ => 24
  | .userRefIdx _ => 28

def encode : MassCancelRequestOptionalValue → List UInt8
  | .side message => SideValue.encode message
  | .groupId message => GroupIdValue.encode message
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MassCancelRequestOptionalValue) : (encode message).length ≤ 2 := by
  cases message with
  | side inner =>
    simp only [encode, SideValue.encode_length]
    omega
  | groupId inner =>
    simp only [encode, GroupIdValue.encode_length]
    omega
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (MassCancelRequestOptionalValue × List UInt8) :=
  if tag = 27 then (SideValue.decode bytes).map fun (message, rest) => (.side message, rest)
  else if tag = 24 then (GroupIdValue.decode bytes).map fun (message, rest) => (.groupId message, rest)
  else if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : MassCancelRequestOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end MassCancelRequestOptionalValue

/-- Mass Cancel Request Appendage -/
structure MassCancelRequestAppendage where
  massCancelRequestOptionalValue : MassCancelRequestOptionalValue
  deriving DecidableEq, Repr

namespace MassCancelRequestAppendage

def encodeBody (message : MassCancelRequestAppendage) : List UInt8 :=
  encodeUInt 1 (MassCancelRequestOptionalValue.tag message.massCancelRequestOptionalValue)
    ++ (MassCancelRequestOptionalValue.encode message.massCancelRequestOptionalValue)

def decodeBody (bytes : List UInt8) : Option (MassCancelRequestAppendage × List UInt8) := do
  let (massCancelRequestOptionalField, bytes) ← decodeUInt 1 bytes
  let (massCancelRequestOptionalValue, bytes) ← MassCancelRequestOptionalValue.decode massCancelRequestOptionalField bytes
  pure ({ massCancelRequestOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : MassCancelRequestAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [MassCancelRequestOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : MassCancelRequestAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.massCancelRequestOptionalValue with
  | side inner =>
    simp only [MassCancelRequestOptionalValue.encode, List.length_append, encodeUInt_length, SideValue.encode_length]
    omega
  | groupId inner =>
    simp only [MassCancelRequestOptionalValue.encode, List.length_append, encodeUInt_length, GroupIdValue.encode_length]
    omega
  | userRefIdx inner =>
    simp only [MassCancelRequestOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : MassCancelRequestAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (MassCancelRequestAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : MassCancelRequestAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : MassCancelRequestAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end MassCancelRequestAppendage

/-- Mass Cancel Request Message -/
structure MassCancelRequestMessage where
  userRefNum : BitVec 32
  firm : Alpha 4
  symbol : Alpha 8
  massCancelRequestAppendage : Sized 2 MassCancelRequestAppendage.encode
  deriving DecidableEq, Repr

namespace MassCancelRequestMessage

def encode (message : MassCancelRequestMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.firm
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany MassCancelRequestAppendage.encode message.massCancelRequestAppendage.val).length)
    ++ (encodeMany MassCancelRequestAppendage.encode message.massCancelRequestAppendage.val))))

def decode (bytes : List UInt8) : Option (MassCancelRequestMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (massCancelRequestAppendage_, bytes) ← decodeSized MassCancelRequestAppendage.decode appendageLength.toNat bytes
  if fits_massCancelRequestAppendage : (encodeMany MassCancelRequestAppendage.encode massCancelRequestAppendage_).length < 256 ^ 2 then
    pure ({ userRefNum, firm, symbol, massCancelRequestAppendage := ⟨massCancelRequestAppendage_, fits_massCancelRequestAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassCancelRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassCancelRequestMessage) : (encode message).length ≤ 65553 := by
  have bound_massCancelRequestAppendage := message.massCancelRequestAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MassCancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 MassCancelRequestAppendage.encode MassCancelRequestAppendage.decode MassCancelRequestAppendage.decode_encode MassCancelRequestAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.massCancelRequestAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MassCancelRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MassCancelRequestMessage

/-- Any Disable Order Entry Request Optional Value, selected by Disable Order Entry Request Optional Field -/
inductive DisableOrderEntryRequestOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace DisableOrderEntryRequestOptionalValue

/-- The Disable Order Entry Request Optional Field each message is sent under -/
def tag : DisableOrderEntryRequestOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : DisableOrderEntryRequestOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : DisableOrderEntryRequestOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (DisableOrderEntryRequestOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : DisableOrderEntryRequestOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end DisableOrderEntryRequestOptionalValue

/-- Disable Order Entry Request Appendage -/
structure DisableOrderEntryRequestAppendage where
  disableOrderEntryRequestOptionalValue : DisableOrderEntryRequestOptionalValue
  deriving DecidableEq, Repr

namespace DisableOrderEntryRequestAppendage

def encodeBody (message : DisableOrderEntryRequestAppendage) : List UInt8 :=
  encodeUInt 1 (DisableOrderEntryRequestOptionalValue.tag message.disableOrderEntryRequestOptionalValue)
    ++ (DisableOrderEntryRequestOptionalValue.encode message.disableOrderEntryRequestOptionalValue)

def decodeBody (bytes : List UInt8) : Option (DisableOrderEntryRequestAppendage × List UInt8) := do
  let (disableOrderEntryRequestOptionalField, bytes) ← decodeUInt 1 bytes
  let (disableOrderEntryRequestOptionalValue, bytes) ← DisableOrderEntryRequestOptionalValue.decode disableOrderEntryRequestOptionalField bytes
  pure ({ disableOrderEntryRequestOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : DisableOrderEntryRequestAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [DisableOrderEntryRequestOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : DisableOrderEntryRequestAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.disableOrderEntryRequestOptionalValue with
  | userRefIdx inner =>
    simp only [DisableOrderEntryRequestOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : DisableOrderEntryRequestAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (DisableOrderEntryRequestAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : DisableOrderEntryRequestAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : DisableOrderEntryRequestAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end DisableOrderEntryRequestAppendage

/-- Disable Order Entry Request Message -/
structure DisableOrderEntryRequestMessage where
  userRefNum : BitVec 32
  firm : Alpha 4
  disableOrderEntryRequestAppendage : Sized 2 DisableOrderEntryRequestAppendage.encode
  deriving DecidableEq, Repr

namespace DisableOrderEntryRequestMessage

def encode (message : DisableOrderEntryRequestMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.firm
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany DisableOrderEntryRequestAppendage.encode message.disableOrderEntryRequestAppendage.val).length)
    ++ (encodeMany DisableOrderEntryRequestAppendage.encode message.disableOrderEntryRequestAppendage.val)))

def decode (bytes : List UInt8) : Option (DisableOrderEntryRequestMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (disableOrderEntryRequestAppendage_, bytes) ← decodeSized DisableOrderEntryRequestAppendage.decode appendageLength.toNat bytes
  if fits_disableOrderEntryRequestAppendage : (encodeMany DisableOrderEntryRequestAppendage.encode disableOrderEntryRequestAppendage_).length < 256 ^ 2 then
    pure ({ userRefNum, firm, disableOrderEntryRequestAppendage := ⟨disableOrderEntryRequestAppendage_, fits_disableOrderEntryRequestAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : DisableOrderEntryRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DisableOrderEntryRequestMessage) : (encode message).length ≤ 65545 := by
  have bound_disableOrderEntryRequestAppendage := message.disableOrderEntryRequestAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : DisableOrderEntryRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 DisableOrderEntryRequestAppendage.encode DisableOrderEntryRequestAppendage.decode DisableOrderEntryRequestAppendage.decode_encode DisableOrderEntryRequestAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.disableOrderEntryRequestAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DisableOrderEntryRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DisableOrderEntryRequestMessage

/-- Any Enable Order Entry Request Optional Value, selected by Enable Order Entry Request Optional Field -/
inductive EnableOrderEntryRequestOptionalValue where
  | userRefIdx (message : UserRefIdxValue) -- 28
  deriving DecidableEq, Repr

namespace EnableOrderEntryRequestOptionalValue

/-- The Enable Order Entry Request Optional Field each message is sent under -/
def tag : EnableOrderEntryRequestOptionalValue → BitVec 8
  | .userRefIdx _ => 28

def encode : EnableOrderEntryRequestOptionalValue → List UInt8
  | .userRefIdx message => UserRefIdxValue.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : EnableOrderEntryRequestOptionalValue) : (encode message).length ≤ 1 := by
  cases message with
  | userRefIdx inner =>
    simp only [encode, UserRefIdxValue.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (EnableOrderEntryRequestOptionalValue × List UInt8) :=
  if tag = 28 then (UserRefIdxValue.decode bytes).map fun (message, rest) => (.userRefIdx message, rest)
  else none

@[simp] theorem decode_encode (message : EnableOrderEntryRequestOptionalValue) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end EnableOrderEntryRequestOptionalValue

/-- Enable Order Entry Request Appendage -/
structure EnableOrderEntryRequestAppendage where
  enableOrderEntryRequestOptionalValue : EnableOrderEntryRequestOptionalValue
  deriving DecidableEq, Repr

namespace EnableOrderEntryRequestAppendage

def encodeBody (message : EnableOrderEntryRequestAppendage) : List UInt8 :=
  encodeUInt 1 (EnableOrderEntryRequestOptionalValue.tag message.enableOrderEntryRequestOptionalValue)
    ++ (EnableOrderEntryRequestOptionalValue.encode message.enableOrderEntryRequestOptionalValue)

def decodeBody (bytes : List UInt8) : Option (EnableOrderEntryRequestAppendage × List UInt8) := do
  let (enableOrderEntryRequestOptionalField, bytes) ← decodeUInt 1 bytes
  let (enableOrderEntryRequestOptionalValue, bytes) ← EnableOrderEntryRequestOptionalValue.decode enableOrderEntryRequestOptionalField bytes
  pure ({ enableOrderEntryRequestOptionalValue }, bytes)

theorem decodeBody_encodeBody (message : EnableOrderEntryRequestAppendage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EnableOrderEntryRequestOptionalValue.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : EnableOrderEntryRequestAppendage) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.enableOrderEntryRequestOptionalValue with
  | userRefIdx inner =>
    simp only [EnableOrderEntryRequestOptionalValue.encode, List.length_append, encodeUInt_length, UserRefIdxValue.encode_length]
    omega

/-- Size rule: Optional Field Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : EnableOrderEntryRequestAppendage → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (EnableOrderEntryRequestAppendage × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : EnableOrderEntryRequestAppendage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : EnableOrderEntryRequestAppendage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end EnableOrderEntryRequestAppendage

/-- Enable Order Entry Request Message -/
structure EnableOrderEntryRequestMessage where
  userRefNum : BitVec 32
  firm : Alpha 4
  enableOrderEntryRequestAppendage : Sized 2 EnableOrderEntryRequestAppendage.encode
  deriving DecidableEq, Repr

namespace EnableOrderEntryRequestMessage

def encode (message : EnableOrderEntryRequestMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.firm
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany EnableOrderEntryRequestAppendage.encode message.enableOrderEntryRequestAppendage.val).length)
    ++ (encodeMany EnableOrderEntryRequestAppendage.encode message.enableOrderEntryRequestAppendage.val)))

def decode (bytes : List UInt8) : Option (EnableOrderEntryRequestMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (firm, bytes) ← Alpha.decode 4 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (enableOrderEntryRequestAppendage_, bytes) ← decodeSized EnableOrderEntryRequestAppendage.decode appendageLength.toNat bytes
  if fits_enableOrderEntryRequestAppendage : (encodeMany EnableOrderEntryRequestAppendage.encode enableOrderEntryRequestAppendage_).length < 256 ^ 2 then
    pure ({ userRefNum, firm, enableOrderEntryRequestAppendage := ⟨enableOrderEntryRequestAppendage_, fits_enableOrderEntryRequestAppendage⟩ }, bytes)
  else none

theorem encode_length_pos (message : EnableOrderEntryRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EnableOrderEntryRequestMessage) : (encode message).length ≤ 65545 := by
  have bound_enableOrderEntryRequestAppendage := message.enableOrderEntryRequestAppendage.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : EnableOrderEntryRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 EnableOrderEntryRequestAppendage.encode EnableOrderEntryRequestAppendage.decode EnableOrderEntryRequestAppendage.decode_encode EnableOrderEntryRequestAppendage.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.enableOrderEntryRequestAppendage.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EnableOrderEntryRequestMessage) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EnableOrderEntryRequestMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | enterOrderMessage (message : EnterOrderMessage) -- 'O' 0x4F
  | replaceOrderMessage (message : ReplaceOrderMessage) -- 'U' 0x55
  | cancelOrderMessage (message : CancelOrderMessage) -- 'X' 0x58
  | modifyOrderMessage (message : ModifyOrderMessage) -- 'M' 0x4D
  | accountQueryMessage (message : AccountQueryMessage) -- 'Q' 0x51
  | massCancelRequestMessage (message : MassCancelRequestMessage) -- 'C' 0x43
  | disableOrderEntryRequestMessage (message : DisableOrderEntryRequestMessage) -- 'D' 0x44
  | enableOrderEntryRequestMessage (message : EnableOrderEntryRequestMessage) -- 'E' 0x45
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .enterOrderMessage _ => 79
  | .replaceOrderMessage _ => 85
  | .cancelOrderMessage _ => 88
  | .modifyOrderMessage _ => 77
  | .accountQueryMessage _ => 81
  | .massCancelRequestMessage _ => 67
  | .disableOrderEntryRequestMessage _ => 68
  | .enableOrderEntryRequestMessage _ => 69

def encode : UnsequencedMessage → List UInt8
  | .enterOrderMessage message => EnterOrderMessage.encode message
  | .replaceOrderMessage message => ReplaceOrderMessage.encode message
  | .cancelOrderMessage message => CancelOrderMessage.encode message
  | .modifyOrderMessage message => ModifyOrderMessage.encode message
  | .accountQueryMessage message => AccountQueryMessage.encode message
  | .massCancelRequestMessage message => MassCancelRequestMessage.encode message
  | .disableOrderEntryRequestMessage message => DisableOrderEntryRequestMessage.encode message
  | .enableOrderEntryRequestMessage message => EnableOrderEntryRequestMessage.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option UnsequencedMessage :=
  if tag = 79 then (EnterOrderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.enterOrderMessage message) else none
  else if tag = 85 then (ReplaceOrderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.replaceOrderMessage message) else none
  else if tag = 88 then (CancelOrderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.cancelOrderMessage message) else none
  else if tag = 77 then (ModifyOrderMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.modifyOrderMessage message) else none
  else if tag = 81 then (AccountQueryMessage.decode bytes).map fun message => .accountQueryMessage message
  else if tag = 67 then (MassCancelRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.massCancelRequestMessage message) else none
  else if tag = 68 then (DisableOrderEntryRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.disableOrderEntryRequestMessage message) else none
  else if tag = 69 then (EnableOrderEntryRequestMessage.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.enableOrderEntryRequestMessage message) else none
  else none

theorem decode_encode (message : UnsequencedMessage) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | enterOrderMessage message => simp [decode, encode, tag, EnterOrderMessage.decode_encode_nil]
  | replaceOrderMessage message => simp [decode, encode, tag, ReplaceOrderMessage.decode_encode_nil]
  | cancelOrderMessage message => simp [decode, encode, tag, CancelOrderMessage.decode_encode_nil]
  | modifyOrderMessage message => simp [decode, encode, tag, ModifyOrderMessage.decode_encode_nil]
  | accountQueryMessage message => simp [decode, encode, tag, AccountQueryMessage.decode_encode]
  | massCancelRequestMessage message => simp [decode, encode, tag, MassCancelRequestMessage.decode_encode_nil]
  | disableOrderEntryRequestMessage message => simp [decode, encode, tag, DisableOrderEntryRequestMessage.decode_encode_nil]
  | enableOrderEntryRequestMessage message => simp [decode, encode, tag, EnableOrderEntryRequestMessage.decode_encode_nil]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option UnsequencedDataPacket := do
  let (unsequencedMessageType, bytes) ← decodeUInt 1 bytes
  let unsequencedMessage ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure { unsequencedMessage }

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

theorem decode_encode (message : UnsequencedDataPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

end UnsequencedDataPacket

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

/-- Logout Request: 0 bytes -/
structure LogoutRequest where
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (_ : LogoutRequest) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequest × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequest) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogoutRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LogoutRequest

/-- Any Client Payload, selected by Client Packet Type -/
inductive ClientPayload where
  | debugPacket (message : DebugPacket) -- '+' 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- 'L' 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- 'U' 0x55
  | clientHeartbeat (message : ClientHeartbeat) -- 'R' 0x52
  | logoutRequest (message : LogoutRequest) -- 'O' 0x4F
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .unsequencedDataPacket _ => 85
  | .clientHeartbeat _ => 82
  | .logoutRequest _ => 79

def encode : ClientPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message
  | .logoutRequest message => LogoutRequest.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option ClientPayload :=
  if tag = 43 then (DebugPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.debugPacket message) else none
  else if tag = 76 then (LoginRequestPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequestPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).map fun message => .unsequencedDataPacket message
  else if tag = 82 then (ClientHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clientHeartbeat message) else none
  else if tag = 79 then (LogoutRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logoutRequest message) else none
  else none

theorem decode_encode (message : ClientPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | debugPacket message => simp [decode, encode, tag, DebugPacket.decode_encode_nil]
  | loginRequestPacket message => simp [decode, encode, tag, LoginRequestPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode]
  | clientHeartbeat message => simp [decode, encode, tag, ClientHeartbeat.decode_encode_nil]
  | logoutRequest message => simp [decode, encode, tag, LogoutRequest.decode_encode_nil]

end ClientPayload

/-- Client Soup Bin Tcp Packet: the body, which the record carries with the proof it fits its frame -/
structure ClientSoupBinTcpPacketBody where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSoupBinTcpPacketBody

def encodeBody (message : ClientSoupBinTcpPacketBody) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option ClientSoupBinTcpPacketBody := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let clientPayload ← ClientPayload.decode clientPacketType bytes
  pure { clientPayload }

theorem decodeBody_encodeBody (message : ClientSoupBinTcpPacketBody) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

end ClientSoupBinTcpPacketBody

/-- Client Soup Bin Tcp Packet: the body with the proof its encoding fits Packet Length, whose 2 bytes no bound of the fields fits -/
abbrev ClientSoupBinTcpPacket := Fitting ClientSoupBinTcpPacketBody.encodeBody 0 65536

namespace ClientSoupBinTcpPacket

def encode (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeFramed 2 0 ClientSoupBinTcpPacketBody.encodeBody message.val

def decode : List UInt8 → Option (ClientSoupBinTcpPacket × List UInt8) :=
  decodeFittingAll 2 0 ClientSoupBinTcpPacketBody.encodeBody ClientSoupBinTcpPacketBody.decodeBody

@[simp] theorem decode_encode (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFittingAll_encodeFramed 2 0 ClientSoupBinTcpPacketBody.encodeBody ClientSoupBinTcpPacketBody.decodeBody message (ClientSoupBinTcpPacketBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : ClientSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : ClientSoupBinTcpPacket) : (encode message).length ≤ 65537 := by
  have fits := message.fits
  unfold encode
  rw [encodeFramed_length]
  omega

end ClientSoupBinTcpPacket

/-- Client Packet -/
structure ClientPacket where
  clientSoupBinTcpPacket : List ClientSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientSoupBinTcpPacket.encode message.clientSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientSoupBinTcpPacket ← decodeAll ClientSoupBinTcpPacket.decode bytes.length bytes
  pure { clientSoupBinTcpPacket }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.decode ClientSoupBinTcpPacket.decode_encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket _ (encodeMany_length_ge ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket), some_bind]
  rfl

end ClientPacket

end Omi.NasdaqNsmequitiesOrdersOuchV50Client
