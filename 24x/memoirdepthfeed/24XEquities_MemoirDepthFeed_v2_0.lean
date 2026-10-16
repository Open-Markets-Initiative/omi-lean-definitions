import Wire

/-!
# 24 National Exchange Member Order Information Record Depth Feed v2.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.N24x24xequitiesMemoirdepthfeedSbeV20

/-- Security Trading Status: one byte code -/
def SecurityTradingStatus.codes : List UInt8 :=
  [0x48, 0x50, 0x51, 0x54]

inductive SecurityTradingStatus where
  | halted -- Halted
  | paused -- Paused
  | quoting -- Quoting
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityTradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityTradingStatus

def toByte : SecurityTradingStatus → UInt8
  | .halted => 0x48
  | .paused => 0x50
  | .quoting => 0x51
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityTradingStatus :=
  if byte = 0x48 then .halted
  else if byte = 0x50 then .paused
  else if byte = 0x51 then .quoting
  else .trading

def ofByte (byte : UInt8) : SecurityTradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityTradingStatus) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | paused => decide
  | quoting => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityTradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityTradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityTradingStatus) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecurityTradingStatus) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecurityTradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityTradingStatus

/-- Security Trading Status Reason: one byte code -/
def SecurityTradingStatusReason.codes : List UInt8 :=
  [0x58, 0x52, 0x41]

inductive SecurityTradingStatusReason where
  | none_ -- None
  | regulatory -- Regulatory
  | administrative -- Administrative
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityTradingStatusReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityTradingStatusReason

def toByte : SecurityTradingStatusReason → UInt8
  | .none_ => 0x58
  | .regulatory => 0x52
  | .administrative => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityTradingStatusReason :=
  if byte = 0x58 then .none_
  else if byte = 0x52 then .regulatory
  else .administrative

def ofByte (byte : UInt8) : SecurityTradingStatusReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityTradingStatusReason) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | regulatory => decide
  | administrative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityTradingStatusReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityTradingStatusReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityTradingStatusReason) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SecurityTradingStatusReason) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SecurityTradingStatusReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityTradingStatusReason

/-- Trading Session: one byte code -/
def TradingSession.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34]

inductive TradingSession where
  | overnight -- Overnight
  | opening -- Opening
  | trading -- Trading
  | postTrading -- Post Trading
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingSession.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingSession

def toByte : TradingSession → UInt8
  | .overnight => 0x30
  | .opening => 0x31
  | .trading => 0x32
  | .postTrading => 0x33
  | .closed => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingSession :=
  if byte = 0x30 then .overnight
  else if byte = 0x31 then .opening
  else if byte = 0x32 then .trading
  else if byte = 0x33 then .postTrading
  else .closed

def ofByte (byte : UInt8) : TradingSession :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingSession) : ofByte value.toByte = value := by
  cases value with
  | overnight => decide
  | opening => decide
  | trading => decide
  | postTrading => decide
  | closed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingSession) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingSession × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingSession) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : TradingSession) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : TradingSession) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingSession

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Side) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x20, 0x4F, 0x43, 0x48, 0x49, 0x50]

inductive AuctionType where
  | unknown -- Unknown
  | opening -- Opening
  | closing -- Closing
  | halt -- Halt
  | ipo -- Ipo
  | pause -- Pause
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .unknown => 0x20
  | .opening => 0x4F
  | .closing => 0x43
  | .halt => 0x48
  | .ipo => 0x49
  | .pause => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x20 then .unknown
  else if byte = 0x4F then .opening
  else if byte = 0x43 then .closing
  else if byte = 0x48 then .halt
  else if byte = 0x49 then .ipo
  else .pause

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | unknown => decide
  | opening => decide
  | closing => decide
  | halt => decide
  | ipo => decide
  | pause => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : AuctionType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : AuctionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionType

/-- Sale Condition 1: one byte code -/
def SaleCondition1.codes : List UInt8 :=
  [0x40]

inductive SaleCondition1 where
  | regularTrade -- Regular Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleCondition1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleCondition1

def toByte : SaleCondition1 → UInt8
  | .regularTrade => 0x40
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : SaleCondition1 :=
  .regularTrade

def ofByte (byte : UInt8) : SaleCondition1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleCondition1) : ofByte value.toByte = value := by
  cases value with
  | regularTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleCondition1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleCondition1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleCondition1) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SaleCondition1) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SaleCondition1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleCondition1

/-- Sale Condition 2: one byte code -/
def SaleCondition2.codes : List UInt8 :=
  [0x20, 0x4F, 0x35, 0x36]

inductive SaleCondition2 where
  | notApplicable -- Not Applicable
  | marketCenterOpeningTrade -- Market Center Opening Trade
  | marketCenterReopeningTrade -- Market Center Reopening Trade
  | marketCenterClosingTrade -- Market Center Closing Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleCondition2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleCondition2

def toByte : SaleCondition2 → UInt8
  | .notApplicable => 0x20
  | .marketCenterOpeningTrade => 0x4F
  | .marketCenterReopeningTrade => 0x35
  | .marketCenterClosingTrade => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleCondition2 :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x4F then .marketCenterOpeningTrade
  else if byte = 0x35 then .marketCenterReopeningTrade
  else .marketCenterClosingTrade

def ofByte (byte : UInt8) : SaleCondition2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleCondition2) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | marketCenterOpeningTrade => decide
  | marketCenterReopeningTrade => decide
  | marketCenterClosingTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleCondition2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleCondition2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleCondition2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SaleCondition2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SaleCondition2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleCondition2

/-- Sale Condition 3: one byte code -/
def SaleCondition3.codes : List UInt8 :=
  [0x20, 0x54]

inductive SaleCondition3 where
  | notApplicable -- Not Applicable
  | formT -- Form T
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleCondition3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleCondition3

def toByte : SaleCondition3 → UInt8
  | .notApplicable => 0x20
  | .formT => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleCondition3 :=
  if byte = 0x20 then .notApplicable
  else .formT

def ofByte (byte : UInt8) : SaleCondition3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleCondition3) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | formT => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleCondition3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleCondition3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleCondition3) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SaleCondition3) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SaleCondition3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleCondition3

/-- Sale Condition 4: one byte code -/
def SaleCondition4.codes : List UInt8 :=
  [0x20, 0x48, 0x49, 0x58]

inductive SaleCondition4 where
  | notApplicable -- Not Applicable
  | priceVariationTrade -- Price Variation Trade
  | oddLotTrade -- Odd Lot Trade
  | auctionTrade -- Auction Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ SaleCondition4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SaleCondition4

def toByte : SaleCondition4 → UInt8
  | .notApplicable => 0x20
  | .priceVariationTrade => 0x48
  | .oddLotTrade => 0x49
  | .auctionTrade => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SaleCondition4 :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x48 then .priceVariationTrade
  else if byte = 0x49 then .oddLotTrade
  else .auctionTrade

def ofByte (byte : UInt8) : SaleCondition4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SaleCondition4) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | priceVariationTrade => decide
  | oddLotTrade => decide
  | auctionTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SaleCondition4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SaleCondition4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SaleCondition4) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SaleCondition4) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SaleCondition4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SaleCondition4

/-- Original Sale Condition 1: one byte code -/
def OriginalSaleCondition1.codes : List UInt8 :=
  [0x40]

inductive OriginalSaleCondition1 where
  | regularTrade -- Regular Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalSaleCondition1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalSaleCondition1

def toByte : OriginalSaleCondition1 → UInt8
  | .regularTrade => 0x40
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : OriginalSaleCondition1 :=
  .regularTrade

def ofByte (byte : UInt8) : OriginalSaleCondition1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalSaleCondition1) : ofByte value.toByte = value := by
  cases value with
  | regularTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalSaleCondition1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalSaleCondition1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalSaleCondition1) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OriginalSaleCondition1) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OriginalSaleCondition1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalSaleCondition1

/-- Original Sale Condition 2: one byte code -/
def OriginalSaleCondition2.codes : List UInt8 :=
  [0x20, 0x4F, 0x35, 0x36]

inductive OriginalSaleCondition2 where
  | notApplicable -- Not Applicable
  | marketCenterOpeningTrade -- Market Center Opening Trade
  | marketCenterReopeningTrade -- Market Center Reopening Trade
  | marketCenterClosingTrade -- Market Center Closing Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalSaleCondition2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalSaleCondition2

def toByte : OriginalSaleCondition2 → UInt8
  | .notApplicable => 0x20
  | .marketCenterOpeningTrade => 0x4F
  | .marketCenterReopeningTrade => 0x35
  | .marketCenterClosingTrade => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalSaleCondition2 :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x4F then .marketCenterOpeningTrade
  else if byte = 0x35 then .marketCenterReopeningTrade
  else .marketCenterClosingTrade

def ofByte (byte : UInt8) : OriginalSaleCondition2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalSaleCondition2) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | marketCenterOpeningTrade => decide
  | marketCenterReopeningTrade => decide
  | marketCenterClosingTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalSaleCondition2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalSaleCondition2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalSaleCondition2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OriginalSaleCondition2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OriginalSaleCondition2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalSaleCondition2

/-- Original Sale Condition 3: one byte code -/
def OriginalSaleCondition3.codes : List UInt8 :=
  [0x20, 0x54]

inductive OriginalSaleCondition3 where
  | notApplicable -- Not Applicable
  | formT -- Form T
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalSaleCondition3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalSaleCondition3

def toByte : OriginalSaleCondition3 → UInt8
  | .notApplicable => 0x20
  | .formT => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalSaleCondition3 :=
  if byte = 0x20 then .notApplicable
  else .formT

def ofByte (byte : UInt8) : OriginalSaleCondition3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalSaleCondition3) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | formT => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalSaleCondition3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalSaleCondition3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalSaleCondition3) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OriginalSaleCondition3) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OriginalSaleCondition3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalSaleCondition3

/-- Original Sale Condition 4: one byte code -/
def OriginalSaleCondition4.codes : List UInt8 :=
  [0x20, 0x48, 0x49, 0x58]

inductive OriginalSaleCondition4 where
  | notApplicable -- Not Applicable
  | priceVariationTrade -- Price Variation Trade
  | oddLotTrade -- Odd Lot Trade
  | auctionTrade -- Auction Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ OriginalSaleCondition4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OriginalSaleCondition4

def toByte : OriginalSaleCondition4 → UInt8
  | .notApplicable => 0x20
  | .priceVariationTrade => 0x48
  | .oddLotTrade => 0x49
  | .auctionTrade => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OriginalSaleCondition4 :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x48 then .priceVariationTrade
  else if byte = 0x49 then .oddLotTrade
  else .auctionTrade

def ofByte (byte : UInt8) : OriginalSaleCondition4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OriginalSaleCondition4) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | priceVariationTrade => decide
  | oddLotTrade => decide
  | auctionTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OriginalSaleCondition4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OriginalSaleCondition4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OriginalSaleCondition4) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : OriginalSaleCondition4) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : OriginalSaleCondition4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OriginalSaleCondition4

/-- Corrected Sale Condition 1: one byte code -/
def CorrectedSaleCondition1.codes : List UInt8 :=
  [0x40]

inductive CorrectedSaleCondition1 where
  | regularTrade -- Regular Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedSaleCondition1.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedSaleCondition1

def toByte : CorrectedSaleCondition1 → UInt8
  | .regularTrade => 0x40
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : CorrectedSaleCondition1 :=
  .regularTrade

def ofByte (byte : UInt8) : CorrectedSaleCondition1 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedSaleCondition1) : ofByte value.toByte = value := by
  cases value with
  | regularTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedSaleCondition1) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedSaleCondition1 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedSaleCondition1) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CorrectedSaleCondition1) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CorrectedSaleCondition1) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedSaleCondition1

/-- Corrected Sale Condition 2: one byte code -/
def CorrectedSaleCondition2.codes : List UInt8 :=
  [0x20, 0x4F, 0x35, 0x36]

inductive CorrectedSaleCondition2 where
  | notApplicable -- Not Applicable
  | marketCenterOpeningTrade -- Market Center Opening Trade
  | marketCenterReopeningTrade -- Market Center Reopening Trade
  | marketCenterClosingTrade -- Market Center Closing Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedSaleCondition2.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedSaleCondition2

def toByte : CorrectedSaleCondition2 → UInt8
  | .notApplicable => 0x20
  | .marketCenterOpeningTrade => 0x4F
  | .marketCenterReopeningTrade => 0x35
  | .marketCenterClosingTrade => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedSaleCondition2 :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x4F then .marketCenterOpeningTrade
  else if byte = 0x35 then .marketCenterReopeningTrade
  else .marketCenterClosingTrade

def ofByte (byte : UInt8) : CorrectedSaleCondition2 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedSaleCondition2) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | marketCenterOpeningTrade => decide
  | marketCenterReopeningTrade => decide
  | marketCenterClosingTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedSaleCondition2) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedSaleCondition2 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedSaleCondition2) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CorrectedSaleCondition2) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CorrectedSaleCondition2) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedSaleCondition2

/-- Corrected Sale Condition 3: one byte code -/
def CorrectedSaleCondition3.codes : List UInt8 :=
  [0x20, 0x54]

inductive CorrectedSaleCondition3 where
  | notApplicable -- Not Applicable
  | formT -- Form T
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedSaleCondition3.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedSaleCondition3

def toByte : CorrectedSaleCondition3 → UInt8
  | .notApplicable => 0x20
  | .formT => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedSaleCondition3 :=
  if byte = 0x20 then .notApplicable
  else .formT

def ofByte (byte : UInt8) : CorrectedSaleCondition3 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedSaleCondition3) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | formT => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedSaleCondition3) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedSaleCondition3 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedSaleCondition3) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CorrectedSaleCondition3) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CorrectedSaleCondition3) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedSaleCondition3

/-- Corrected Sale Condition 4: one byte code -/
def CorrectedSaleCondition4.codes : List UInt8 :=
  [0x20, 0x48, 0x49, 0x58]

inductive CorrectedSaleCondition4 where
  | notApplicable -- Not Applicable
  | priceVariationTrade -- Price Variation Trade
  | oddLotTrade -- Odd Lot Trade
  | auctionTrade -- Auction Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ CorrectedSaleCondition4.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CorrectedSaleCondition4

def toByte : CorrectedSaleCondition4 → UInt8
  | .notApplicable => 0x20
  | .priceVariationTrade => 0x48
  | .oddLotTrade => 0x49
  | .auctionTrade => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CorrectedSaleCondition4 :=
  if byte = 0x20 then .notApplicable
  else if byte = 0x48 then .priceVariationTrade
  else if byte = 0x49 then .oddLotTrade
  else .auctionTrade

def ofByte (byte : UInt8) : CorrectedSaleCondition4 :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CorrectedSaleCondition4) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | priceVariationTrade => decide
  | oddLotTrade => decide
  | auctionTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CorrectedSaleCondition4) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CorrectedSaleCondition4 × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CorrectedSaleCondition4) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : CorrectedSaleCondition4) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : CorrectedSaleCondition4) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CorrectedSaleCondition4

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

/-- Session Shutdown: 0 bytes -/
structure SessionShutdown where
  deriving DecidableEq, Repr

namespace SessionShutdown

def encode (_ : SessionShutdown) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SessionShutdown × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SessionShutdown) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SessionShutdown) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end SessionShutdown

/-- Instrument Directory Message: 27 bytes -/
structure InstrumentDirectoryMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  symbol : Alpha 6
  symbolSfx : Alpha 6
  roundLot : BitVec 32
  isTestSymbol : BitVec 8
  deriving DecidableEq, Repr

namespace InstrumentDirectoryMessage

def encode (message : InstrumentDirectoryMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (encodeUInt 4 message.roundLot
    ++ (encodeUInt 1 message.isTestSymbol)))))

def decode (bytes : List UInt8) : Option (InstrumentDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (roundLot, bytes) ← decodeUInt 4 bytes
  let (isTestSymbol, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, securityId, symbol, symbolSfx, roundLot, isTestSymbol }, bytes)

@[simp] theorem encode_length (message : InstrumentDirectoryMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InstrumentDirectoryMessage

/-- Reg Sho Restriction Message: 11 bytes -/
structure RegShoRestrictionMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  shortSaleRestriction : BitVec 8
  deriving DecidableEq, Repr

namespace RegShoRestrictionMessage

def encode (message : RegShoRestrictionMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 1 message.shortSaleRestriction))

def decode (bytes : List UInt8) : Option (RegShoRestrictionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (shortSaleRestriction, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, securityId, shortSaleRestriction }, bytes)

@[simp] theorem encode_length (message : RegShoRestrictionMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : RegShoRestrictionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegShoRestrictionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RegShoRestrictionMessage

/-- Security Trading Status Message: 13 bytes -/
structure SecurityTradingStatusMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  securityTradingStatus : SecurityTradingStatus
  securityTradingStatusReason : SecurityTradingStatusReason
  haltReason : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityTradingStatusMessage

def encode (message : SecurityTradingStatusMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (SecurityTradingStatus.encode message.securityTradingStatus
    ++ (SecurityTradingStatusReason.encode message.securityTradingStatusReason
    ++ (encodeUInt 1 message.haltReason))))

def decode (bytes : List UInt8) : Option (SecurityTradingStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (securityTradingStatus, bytes) ← SecurityTradingStatus.decode bytes
  let (securityTradingStatusReason, bytes) ← SecurityTradingStatusReason.decode bytes
  let (haltReason, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, securityId, securityTradingStatus, securityTradingStatusReason, haltReason }, bytes)

@[simp] theorem encode_length (message : SecurityTradingStatusMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SecurityTradingStatus.encode_length, SecurityTradingStatusReason.encode_length]

theorem encode_length_pos (message : SecurityTradingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityTradingStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityTradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityTradingStatusReason.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecurityTradingStatusMessage

/-- Trading Session Status Message: 9 bytes -/
structure TradingSessionStatusMessage where
  timestamp : BitVec 64
  tradingSession : TradingSession
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (TradingSession.encode message.tradingSession)

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (tradingSession, bytes) ← TradingSession.decode bytes
  pure ({ timestamp, tradingSession }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingSession.encode_length]

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TradingSession.decode_encode, some_bind]
  rfl

end TradingSessionStatusMessage

/-- Order Added Message: 32 bytes -/
structure OrderAddedMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  orderId : BitVec 64
  side : Side
  quantity : BitVec 32
  price : BitVec 64
  orderFlags : BitVec 8
  deriving DecidableEq, Repr

namespace OrderAddedMessage

def encode (message : OrderAddedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price
    ++ (encodeUIntLE 1 message.orderFlags))))))

def decode (bytes : List UInt8) : Option (OrderAddedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ timestamp, securityId, orderId, side, quantity, price, orderFlags }, bytes)

@[simp] theorem encode_length (message : OrderAddedMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderAddedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderAddedMessage

/-- Order Deleted Message: 18 bytes -/
structure OrderDeletedMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeletedMessage

def encode (message : OrderDeletedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.orderId))

def decode (bytes : List UInt8) : Option (OrderDeletedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, orderId }, bytes)

@[simp] theorem encode_length (message : OrderDeletedMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderDeletedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeletedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeletedMessage

/-- Order Reduced Message: 22 bytes -/
structure OrderReducedMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  orderId : BitVec 64
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReducedMessage

def encode (message : OrderReducedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.quantity)))

def decode (bytes : List UInt8) : Option (OrderReducedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, securityId, orderId, quantity }, bytes)

@[simp] theorem encode_length (message : OrderReducedMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderReducedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReducedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderReducedMessage

/-- Order Executed Message: 38 bytes -/
structure OrderExecutedMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  orderId : BitVec 64
  tradeId : BitVec 64
  quantity : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price)))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, orderId, tradeId, quantity, price }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedMessage

/-- Trade Message: 30 bytes -/
structure TradeMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  tradeId : BitVec 64
  quantity : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, tradeId, quantity, price }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeMessage

/-- Broken Trade Message: 30 bytes -/
structure BrokenTradeMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  tradeId : BitVec 64
  originalQuantity : BitVec 32
  originalPrice : BitVec 64
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.originalQuantity
    ++ (encodeUInt 8 message.originalPrice))))

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (originalQuantity, bytes) ← decodeUInt 4 bytes
  let (originalPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, tradeId, originalQuantity, originalPrice }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BrokenTradeMessage

/-- Corrected Trade Message: 42 bytes -/
structure CorrectedTradeMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  tradeId : BitVec 64
  originalQuantity : BitVec 32
  originalPrice : BitVec 64
  correctedQuantity : BitVec 32
  correctedPrice : BitVec 64
  deriving DecidableEq, Repr

namespace CorrectedTradeMessage

def encode (message : CorrectedTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.originalQuantity
    ++ (encodeUInt 8 message.originalPrice
    ++ (encodeUInt 4 message.correctedQuantity
    ++ (encodeUInt 8 message.correctedPrice))))))

def decode (bytes : List UInt8) : Option (CorrectedTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (originalQuantity, bytes) ← decodeUInt 4 bytes
  let (originalPrice, bytes) ← decodeUInt 8 bytes
  let (correctedQuantity, bytes) ← decodeUInt 4 bytes
  let (correctedPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, tradeId, originalQuantity, originalPrice, correctedQuantity, correctedPrice }, bytes)

@[simp] theorem encode_length (message : CorrectedTradeMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : CorrectedTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CorrectedTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CorrectedTradeMessage

/-- Clear Book Message: 10 bytes -/
structure ClearBookMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  deriving DecidableEq, Repr

namespace ClearBookMessage

def encode (message : ClearBookMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId)

def decode (bytes : List UInt8) : Option (ClearBookMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  pure ({ timestamp, securityId }, bytes)

@[simp] theorem encode_length (message : ClearBookMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ClearBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearBookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ClearBookMessage

/-- Auction Status Message: 87 bytes -/
structure AuctionStatusMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  auctionId : BitVec 64
  auctionType : AuctionType
  tieBreakerPrice : BitVec 64
  lowerCollarPrice : BitVec 64
  upperCollarPrice : BitVec 64
  referencePrice : BitVec 64
  referenceBuyQuantity : BitVec 64
  referenceSellQuantity : BitVec 64
  indicativePrice : BitVec 64
  auctionOnlyPrice : BitVec 64
  numberOfExtensions : BitVec 32
  deriving DecidableEq, Repr

namespace AuctionStatusMessage

def encode (message : AuctionStatusMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.auctionId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 8 message.tieBreakerPrice
    ++ (encodeUInt 8 message.lowerCollarPrice
    ++ (encodeUInt 8 message.upperCollarPrice
    ++ (encodeUInt 8 message.referencePrice
    ++ (encodeUInt 8 message.referenceBuyQuantity
    ++ (encodeUInt 8 message.referenceSellQuantity
    ++ (encodeUInt 8 message.indicativePrice
    ++ (encodeUInt 8 message.auctionOnlyPrice
    ++ (encodeUInt 4 message.numberOfExtensions))))))))))))

def decode (bytes : List UInt8) : Option (AuctionStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (auctionId, bytes) ← decodeUInt 8 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (tieBreakerPrice, bytes) ← decodeUInt 8 bytes
  let (lowerCollarPrice, bytes) ← decodeUInt 8 bytes
  let (upperCollarPrice, bytes) ← decodeUInt 8 bytes
  let (referencePrice, bytes) ← decodeUInt 8 bytes
  let (referenceBuyQuantity, bytes) ← decodeUInt 8 bytes
  let (referenceSellQuantity, bytes) ← decodeUInt 8 bytes
  let (indicativePrice, bytes) ← decodeUInt 8 bytes
  let (auctionOnlyPrice, bytes) ← decodeUInt 8 bytes
  let (numberOfExtensions, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, securityId, auctionId, auctionType, tieBreakerPrice, lowerCollarPrice, upperCollarPrice, referencePrice, referenceBuyQuantity, referenceSellQuantity, indicativePrice, auctionOnlyPrice, numberOfExtensions }, bytes)

@[simp] theorem encode_length (message : AuctionStatusMessage) : (encode message).length = 87 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AuctionType.encode_length]

theorem encode_length_pos (message : AuctionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AuctionStatusMessage

/-- Auction Trade Message: 47 bytes -/
structure AuctionTradeMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  auctionId : BitVec 64
  auctionType : AuctionType
  auctionQuantity : BitVec 64
  auctionPrice : BitVec 64
  tradeId : BitVec 64
  saleCondition1 : SaleCondition1
  saleCondition2 : SaleCondition2
  saleCondition3 : SaleCondition3
  saleCondition4 : SaleCondition4
  deriving DecidableEq, Repr

namespace AuctionTradeMessage

def encode (message : AuctionTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.auctionId
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 8 message.auctionQuantity
    ++ (encodeUInt 8 message.auctionPrice
    ++ (encodeUInt 8 message.tradeId
    ++ (SaleCondition1.encode message.saleCondition1
    ++ (SaleCondition2.encode message.saleCondition2
    ++ (SaleCondition3.encode message.saleCondition3
    ++ (SaleCondition4.encode message.saleCondition4))))))))))

def decode (bytes : List UInt8) : Option (AuctionTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (auctionId, bytes) ← decodeUInt 8 bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (auctionQuantity, bytes) ← decodeUInt 8 bytes
  let (auctionPrice, bytes) ← decodeUInt 8 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (saleCondition1, bytes) ← SaleCondition1.decode bytes
  let (saleCondition2, bytes) ← SaleCondition2.decode bytes
  let (saleCondition3, bytes) ← SaleCondition3.decode bytes
  let (saleCondition4, bytes) ← SaleCondition4.decode bytes
  pure ({ timestamp, securityId, auctionId, auctionType, auctionQuantity, auctionPrice, tradeId, saleCondition1, saleCondition2, saleCondition3, saleCondition4 }, bytes)

@[simp] theorem encode_length (message : AuctionTradeMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AuctionType.encode_length, SaleCondition1.encode_length, SaleCondition2.encode_length, SaleCondition3.encode_length, SaleCondition4.encode_length]

theorem encode_length_pos (message : AuctionTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SaleCondition1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleCondition2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SaleCondition3.decode_encode, some_bind]
  dsimp only
  rw [SaleCondition4.decode_encode, some_bind]
  rfl

end AuctionTradeMessage

/-- Broken Auction Trade Message: 42 bytes -/
structure BrokenAuctionTradeMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  auctionId : BitVec 64
  tradeId : BitVec 64
  originalAuctionQuantity : BitVec 64
  originalAuctionPrice : BitVec 64
  deriving DecidableEq, Repr

namespace BrokenAuctionTradeMessage

def encode (message : BrokenAuctionTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.auctionId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 8 message.originalAuctionQuantity
    ++ (encodeUInt 8 message.originalAuctionPrice)))))

def decode (bytes : List UInt8) : Option (BrokenAuctionTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (auctionId, bytes) ← decodeUInt 8 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (originalAuctionQuantity, bytes) ← decodeUInt 8 bytes
  let (originalAuctionPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, auctionId, tradeId, originalAuctionQuantity, originalAuctionPrice }, bytes)

@[simp] theorem encode_length (message : BrokenAuctionTradeMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BrokenAuctionTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenAuctionTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BrokenAuctionTradeMessage

/-- Corrected Auction Trade Message: 66 bytes -/
structure CorrectedAuctionTradeMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  auctionId : BitVec 64
  tradeId : BitVec 64
  originalAuctionQuantity : BitVec 64
  originalAuctionPrice : BitVec 64
  originalSaleCondition1 : OriginalSaleCondition1
  originalSaleCondition2 : OriginalSaleCondition2
  originalSaleCondition3 : OriginalSaleCondition3
  originalSaleCondition4 : OriginalSaleCondition4
  correctedAuctionQuantity : BitVec 64
  correctedAuctionPrice : BitVec 64
  correctedSaleCondition1 : CorrectedSaleCondition1
  correctedSaleCondition2 : CorrectedSaleCondition2
  correctedSaleCondition3 : CorrectedSaleCondition3
  correctedSaleCondition4 : CorrectedSaleCondition4
  deriving DecidableEq, Repr

namespace CorrectedAuctionTradeMessage

def encode (message : CorrectedAuctionTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.auctionId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 8 message.originalAuctionQuantity
    ++ (encodeUInt 8 message.originalAuctionPrice
    ++ (OriginalSaleCondition1.encode message.originalSaleCondition1
    ++ (OriginalSaleCondition2.encode message.originalSaleCondition2
    ++ (OriginalSaleCondition3.encode message.originalSaleCondition3
    ++ (OriginalSaleCondition4.encode message.originalSaleCondition4
    ++ (encodeUInt 8 message.correctedAuctionQuantity
    ++ (encodeUInt 8 message.correctedAuctionPrice
    ++ (CorrectedSaleCondition1.encode message.correctedSaleCondition1
    ++ (CorrectedSaleCondition2.encode message.correctedSaleCondition2
    ++ (CorrectedSaleCondition3.encode message.correctedSaleCondition3
    ++ (CorrectedSaleCondition4.encode message.correctedSaleCondition4)))))))))))))))

def decode (bytes : List UInt8) : Option (CorrectedAuctionTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (auctionId, bytes) ← decodeUInt 8 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (originalAuctionQuantity, bytes) ← decodeUInt 8 bytes
  let (originalAuctionPrice, bytes) ← decodeUInt 8 bytes
  let (originalSaleCondition1, bytes) ← OriginalSaleCondition1.decode bytes
  let (originalSaleCondition2, bytes) ← OriginalSaleCondition2.decode bytes
  let (originalSaleCondition3, bytes) ← OriginalSaleCondition3.decode bytes
  let (originalSaleCondition4, bytes) ← OriginalSaleCondition4.decode bytes
  let (correctedAuctionQuantity, bytes) ← decodeUInt 8 bytes
  let (correctedAuctionPrice, bytes) ← decodeUInt 8 bytes
  let (correctedSaleCondition1, bytes) ← CorrectedSaleCondition1.decode bytes
  let (correctedSaleCondition2, bytes) ← CorrectedSaleCondition2.decode bytes
  let (correctedSaleCondition3, bytes) ← CorrectedSaleCondition3.decode bytes
  let (correctedSaleCondition4, bytes) ← CorrectedSaleCondition4.decode bytes
  pure ({ timestamp, securityId, auctionId, tradeId, originalAuctionQuantity, originalAuctionPrice, originalSaleCondition1, originalSaleCondition2, originalSaleCondition3, originalSaleCondition4, correctedAuctionQuantity, correctedAuctionPrice, correctedSaleCondition1, correctedSaleCondition2, correctedSaleCondition3, correctedSaleCondition4 }, bytes)

@[simp] theorem encode_length (message : CorrectedAuctionTradeMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OriginalSaleCondition1.encode_length, OriginalSaleCondition2.encode_length, OriginalSaleCondition3.encode_length, OriginalSaleCondition4.encode_length, CorrectedSaleCondition1.encode_length, CorrectedSaleCondition2.encode_length, CorrectedSaleCondition3.encode_length, CorrectedSaleCondition4.encode_length]

theorem encode_length_pos (message : CorrectedAuctionTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CorrectedAuctionTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleCondition1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleCondition2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleCondition3.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalSaleCondition4.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedSaleCondition1.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedSaleCondition2.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CorrectedSaleCondition3.decode_encode, some_bind]
  dsimp only
  rw [CorrectedSaleCondition4.decode_encode, some_bind]
  rfl

end CorrectedAuctionTradeMessage

/-- Snapshot Complete Message: 16 bytes -/
structure SnapshotCompleteMessage where
  timestamp : BitVec 64
  asOfSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace SnapshotCompleteMessage

def encode (message : SnapshotCompleteMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 8 message.asOfSequenceNumber)

def decode (bytes : List UInt8) : Option (SnapshotCompleteMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (asOfSequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, asOfSequenceNumber }, bytes)

@[simp] theorem encode_length (message : SnapshotCompleteMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SnapshotCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SnapshotCompleteMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | instrumentDirectoryMessage (message : InstrumentDirectoryMessage) -- 1
  | regShoRestrictionMessage (message : RegShoRestrictionMessage) -- 2
  | securityTradingStatusMessage (message : SecurityTradingStatusMessage) -- 3
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 5
  | orderAddedMessage (message : OrderAddedMessage) -- 10
  | orderDeletedMessage (message : OrderDeletedMessage) -- 11
  | orderReducedMessage (message : OrderReducedMessage) -- 12
  | orderExecutedMessage (message : OrderExecutedMessage) -- 13
  | tradeMessage (message : TradeMessage) -- 14
  | brokenTradeMessage (message : BrokenTradeMessage) -- 15
  | correctedTradeMessage (message : CorrectedTradeMessage) -- 16
  | clearBookMessage (message : ClearBookMessage) -- 18
  | auctionStatusMessage (message : AuctionStatusMessage) -- 19
  | auctionTradeMessage (message : AuctionTradeMessage) -- 20
  | brokenAuctionTradeMessage (message : BrokenAuctionTradeMessage) -- 21
  | correctedAuctionTradeMessage (message : CorrectedAuctionTradeMessage) -- 22
  | snapshotCompleteMessage (message : SnapshotCompleteMessage) -- 100
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 8
  | .instrumentDirectoryMessage _ => 1
  | .regShoRestrictionMessage _ => 2
  | .securityTradingStatusMessage _ => 3
  | .tradingSessionStatusMessage _ => 5
  | .orderAddedMessage _ => 10
  | .orderDeletedMessage _ => 11
  | .orderReducedMessage _ => 12
  | .orderExecutedMessage _ => 13
  | .tradeMessage _ => 14
  | .brokenTradeMessage _ => 15
  | .correctedTradeMessage _ => 16
  | .clearBookMessage _ => 18
  | .auctionStatusMessage _ => 19
  | .auctionTradeMessage _ => 20
  | .brokenAuctionTradeMessage _ => 21
  | .correctedAuctionTradeMessage _ => 22
  | .snapshotCompleteMessage _ => 100

def encode : Payload → List UInt8
  | .instrumentDirectoryMessage message => InstrumentDirectoryMessage.encode message
  | .regShoRestrictionMessage message => RegShoRestrictionMessage.encode message
  | .securityTradingStatusMessage message => SecurityTradingStatusMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .orderAddedMessage message => OrderAddedMessage.encode message
  | .orderDeletedMessage message => OrderDeletedMessage.encode message
  | .orderReducedMessage message => OrderReducedMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .correctedTradeMessage message => CorrectedTradeMessage.encode message
  | .clearBookMessage message => ClearBookMessage.encode message
  | .auctionStatusMessage message => AuctionStatusMessage.encode message
  | .auctionTradeMessage message => AuctionTradeMessage.encode message
  | .brokenAuctionTradeMessage message => BrokenAuctionTradeMessage.encode message
  | .correctedAuctionTradeMessage message => CorrectedAuctionTradeMessage.encode message
  | .snapshotCompleteMessage message => SnapshotCompleteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 87 := by
  cases message with
  | instrumentDirectoryMessage inner =>
    simp only [encode, InstrumentDirectoryMessage.encode_length]
    omega
  | regShoRestrictionMessage inner =>
    simp only [encode, RegShoRestrictionMessage.encode_length]
    omega
  | securityTradingStatusMessage inner =>
    simp only [encode, SecurityTradingStatusMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega
  | orderAddedMessage inner =>
    simp only [encode, OrderAddedMessage.encode_length]
    omega
  | orderDeletedMessage inner =>
    simp only [encode, OrderDeletedMessage.encode_length]
    omega
  | orderReducedMessage inner =>
    simp only [encode, OrderReducedMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | correctedTradeMessage inner =>
    simp only [encode, CorrectedTradeMessage.encode_length]
    omega
  | clearBookMessage inner =>
    simp only [encode, ClearBookMessage.encode_length]
    omega
  | auctionStatusMessage inner =>
    simp only [encode, AuctionStatusMessage.encode_length]
    omega
  | auctionTradeMessage inner =>
    simp only [encode, AuctionTradeMessage.encode_length]
    omega
  | brokenAuctionTradeMessage inner =>
    simp only [encode, BrokenAuctionTradeMessage.encode_length]
    omega
  | correctedAuctionTradeMessage inner =>
    simp only [encode, CorrectedAuctionTradeMessage.encode_length]
    omega
  | snapshotCompleteMessage inner =>
    simp only [encode, SnapshotCompleteMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (InstrumentDirectoryMessage.decode bytes).map fun (message, rest) => (.instrumentDirectoryMessage message, rest)
  else if tag = 2 then (RegShoRestrictionMessage.decode bytes).map fun (message, rest) => (.regShoRestrictionMessage message, rest)
  else if tag = 3 then (SecurityTradingStatusMessage.decode bytes).map fun (message, rest) => (.securityTradingStatusMessage message, rest)
  else if tag = 5 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 10 then (OrderAddedMessage.decode bytes).map fun (message, rest) => (.orderAddedMessage message, rest)
  else if tag = 11 then (OrderDeletedMessage.decode bytes).map fun (message, rest) => (.orderDeletedMessage message, rest)
  else if tag = 12 then (OrderReducedMessage.decode bytes).map fun (message, rest) => (.orderReducedMessage message, rest)
  else if tag = 13 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 14 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 15 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 16 then (CorrectedTradeMessage.decode bytes).map fun (message, rest) => (.correctedTradeMessage message, rest)
  else if tag = 18 then (ClearBookMessage.decode bytes).map fun (message, rest) => (.clearBookMessage message, rest)
  else if tag = 19 then (AuctionStatusMessage.decode bytes).map fun (message, rest) => (.auctionStatusMessage message, rest)
  else if tag = 20 then (AuctionTradeMessage.decode bytes).map fun (message, rest) => (.auctionTradeMessage message, rest)
  else if tag = 21 then (BrokenAuctionTradeMessage.decode bytes).map fun (message, rest) => (.brokenAuctionTradeMessage message, rest)
  else if tag = 22 then (CorrectedAuctionTradeMessage.decode bytes).map fun (message, rest) => (.correctedAuctionTradeMessage message, rest)
  else if tag = 100 then (SnapshotCompleteMessage.decode bytes).map fun (message, rest) => (.snapshotCompleteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Sbe Message -/
structure SbeMessage where
  blockLength : BitVec 16
  schemaId : BitVec 8
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace SbeMessage

def encode (message : SbeMessage) : List UInt8 :=
  encodeUInt 2 message.blockLength
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUInt 1 message.schemaId
    ++ (encodeUInt 2 message.version
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (SbeMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUInt 2 bytes
  let (templateId, bytes) ← decodeUInt 1 bytes
  let (schemaId, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem encode_length_pos (message : SbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SbeMessage) : (encode message).length ≤ 93 := by
  unfold encode
  cases message.payload with
  | instrumentDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, InstrumentDirectoryMessage.encode_length]
    omega
  | regShoRestrictionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RegShoRestrictionMessage.encode_length]
    omega
  | securityTradingStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SecurityTradingStatusMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradingSessionStatusMessage.encode_length]
    omega
  | orderAddedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderAddedMessage.encode_length]
    omega
  | orderDeletedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderDeletedMessage.encode_length]
    omega
  | orderReducedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderReducedMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | correctedTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CorrectedTradeMessage.encode_length]
    omega
  | clearBookMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ClearBookMessage.encode_length]
    omega
  | auctionStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, AuctionStatusMessage.encode_length]
    omega
  | auctionTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, AuctionTradeMessage.encode_length]
    omega
  | brokenAuctionTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BrokenAuctionTradeMessage.encode_length]
    omega
  | correctedAuctionTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CorrectedAuctionTradeMessage.encode_length]
    omega
  | snapshotCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SnapshotCompleteMessage.encode_length]
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
  rw [Payload.decode_encode, some_bind]
  rfl

end SbeMessage

/-- Message -/
structure Message where
  sbeMessage : SbeMessage
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  SbeMessage.encode message.sbeMessage

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (sbeMessage, bytes) ← SbeMessage.decode bytes
  pure ({ sbeMessage }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [SbeMessage.decode_encode, some_bind]
  rfl

/-- Size rule: Message Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end Message

/-- Sequenced Message -/
structure SequencedMessage where
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace SequencedMessage

def encode (message : SequencedMessage) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)

def decode (bytes : List UInt8) : Option (SequencedMessage × List UInt8) := do
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : SequencedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end SequencedMessage

/-- Any Sequenced Messages, selected by Message Type -/
inductive SequencedMessages where
  | heartbeat (message : Heartbeat) -- 0
  | sessionShutdown (message : SessionShutdown) -- 1
  | sequencedMessage (message : SequencedMessage) -- 2
  deriving DecidableEq, Repr

namespace SequencedMessages

/-- The Message Type each message is sent under -/
def tag : SequencedMessages → BitVec 8
  | .heartbeat _ => 0
  | .sessionShutdown _ => 1
  | .sequencedMessage _ => 2

def encode : SequencedMessages → List UInt8
  | .heartbeat message => Heartbeat.encode message
  | .sessionShutdown message => SessionShutdown.encode message
  | .sequencedMessage message => SequencedMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessages × List UInt8) :=
  if tag = 0 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 1 then (SessionShutdown.decode bytes).map fun (message, rest) => (.sessionShutdown message, rest)
  else if tag = 2 then (SequencedMessage.decode bytes).map fun (message, rest) => (.sequencedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessages) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessages

/-- Packet -/
structure Packet where
  headerLength : BitVec 8
  sessionId : BitVec 64
  sequenceNumber : BitVec 64
  sequencedMessages : SequencedMessages
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 (SequencedMessages.tag message.sequencedMessages)
    ++ (encodeUInt 1 message.headerLength
    ++ (encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (SequencedMessages.encode message.sequencedMessages))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (headerLength, bytes) ← decodeUInt 1 bytes
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (sequencedMessages, bytes) ← SequencedMessages.decode messageType bytes
  pure ({ headerLength, sessionId, sequenceNumber, sequencedMessages }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
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
  rw [SequencedMessages.decode_encode, some_bind]
  rfl

end Packet

end Omi.N24x24xequitiesMemoirdepthfeedSbeV20
