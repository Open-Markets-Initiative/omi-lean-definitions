import Omi.Wire

/-!
# TMX Group Quantum Feed Level 2 v2.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Packet's Message Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxTsxalphaQuantumfeedlevel2XmtV22

/-- Protocol Name: one byte code -/
def ProtocolName.codes : List UInt8 :=
  [0x58]

inductive ProtocolName where
  | xmt -- Xmt
  | unlisted (byte : { byte : UInt8 // byte ∉ ProtocolName.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProtocolName

def toByte : ProtocolName → UInt8
  | .xmt => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ProtocolName :=
  .xmt

def ofByte (byte : UInt8) : ProtocolName :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProtocolName) : ofByte value.toByte = value := by
  cases value with
  | xmt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ProtocolName) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ProtocolName × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ProtocolName) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ProtocolName) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ProtocolName

/-- Ack Required Poss Dup: one byte code -/
def AckRequiredPossDup.codes : List UInt8 :=
  [0x30]

inductive AckRequiredPossDup where
  | unused -- Unused
  | unlisted (byte : { byte : UInt8 // byte ∉ AckRequiredPossDup.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AckRequiredPossDup

def toByte : AckRequiredPossDup → UInt8
  | .unused => 0x30
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : AckRequiredPossDup :=
  .unused

def ofByte (byte : UInt8) : AckRequiredPossDup :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AckRequiredPossDup) : ofByte value.toByte = value := by
  cases value with
  | unused => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AckRequiredPossDup) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AckRequiredPossDup × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AckRequiredPossDup) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AckRequiredPossDup) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AckRequiredPossDup

/-- Listing Market: one byte code -/
def ListingMarket.codes : List UInt8 :=
  [0x54, 0x56]

inductive ListingMarket where
  | tsx -- Tsx
  | tsxv -- Tsxv
  | unlisted (byte : { byte : UInt8 // byte ∉ ListingMarket.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListingMarket

def toByte : ListingMarket → UInt8
  | .tsx => 0x54
  | .tsxv => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListingMarket :=
  if byte = 0x54 then .tsx
  else .tsxv

def ofByte (byte : UInt8) : ListingMarket :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListingMarket) : ofByte value.toByte = value := by
  cases value with
  | tsx => decide
  | tsxv => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ListingMarket) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ListingMarket × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ListingMarket) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ListingMarket) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ListingMarket

/-- Product Type: one byte code -/
def ProductType.codes : List UInt8 :=
  [0x42, 0x45, 0x4D, 0x46]

inductive ProductType where
  | debenture -- Debenture
  | equity -- Equity
  | mutualFund -- Mutual Fund
  | etf -- Etf
  | unlisted (byte : { byte : UInt8 // byte ∉ ProductType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ProductType

def toByte : ProductType → UInt8
  | .debenture => 0x42
  | .equity => 0x45
  | .mutualFund => 0x4D
  | .etf => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ProductType :=
  if byte = 0x42 then .debenture
  else if byte = 0x45 then .equity
  else if byte = 0x4D then .mutualFund
  else .etf

def ofByte (byte : UInt8) : ProductType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ProductType) : ofByte value.toByte = value := by
  cases value with
  | debenture => decide
  | equity => decide
  | mutualFund => decide
  | etf => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ProductType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ProductType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ProductType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ProductType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ProductType

/-- Currency: one byte code -/
def Currency.codes : List UInt8 :=
  [0x55, 0x43]

inductive Currency where
  | usd -- Usd
  | cad -- Cad
  | unlisted (byte : { byte : UInt8 // byte ∉ Currency.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Currency

def toByte : Currency → UInt8
  | .usd => 0x55
  | .cad => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Currency :=
  if byte = 0x55 then .usd
  else .cad

def ofByte (byte : UInt8) : Currency :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Currency) : ofByte value.toByte = value := by
  cases value with
  | usd => decide
  | cad => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Currency) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Currency × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Currency) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Currency) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Currency

/-- Test Symbol: one byte code -/
def TestSymbol.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TestSymbol where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ TestSymbol.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TestSymbol

def toByte : TestSymbol → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TestSymbol :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : TestSymbol :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TestSymbol) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TestSymbol) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TestSymbol × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TestSymbol) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TestSymbol) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TestSymbol

/-- Order Side: one byte code -/
def OrderSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive OrderSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderSide

def toByte : OrderSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : OrderSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderSide

/-- Market State: one byte code -/
def MarketState.codes : List UInt8 :=
  [0x50, 0x4F, 0x53, 0x43, 0x52, 0x46, 0x4E, 0x4D, 0x41, 0x45, 0x4C]

inductive MarketState where
  | preopen -- Preopen
  | opening -- Opening
  | open_ -- Open
  | closed -- Closed
  | extendedHoursOpen -- Extended Hours Open
  | extendedHoursClose -- Extended Hours Close
  | extendedHoursCxls -- Extended Hours Cxls
  | mocImbalance -- Moc Imbalance
  | ccpDetermination -- Ccp Determination
  | priceMovementExtension -- Price Movement Extension
  | closing -- Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ MarketState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MarketState

def toByte : MarketState → UInt8
  | .preopen => 0x50
  | .opening => 0x4F
  | .open_ => 0x53
  | .closed => 0x43
  | .extendedHoursOpen => 0x52
  | .extendedHoursClose => 0x46
  | .extendedHoursCxls => 0x4E
  | .mocImbalance => 0x4D
  | .ccpDetermination => 0x41
  | .priceMovementExtension => 0x45
  | .closing => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MarketState :=
  if byte = 0x50 then .preopen
  else if byte = 0x4F then .opening
  else if byte = 0x53 then .open_
  else if byte = 0x43 then .closed
  else if byte = 0x52 then .extendedHoursOpen
  else if byte = 0x46 then .extendedHoursClose
  else if byte = 0x4E then .extendedHoursCxls
  else if byte = 0x4D then .mocImbalance
  else if byte = 0x41 then .ccpDetermination
  else if byte = 0x45 then .priceMovementExtension
  else .closing

def ofByte (byte : UInt8) : MarketState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MarketState) : ofByte value.toByte = value := by
  cases value with
  | preopen => decide
  | opening => decide
  | open_ => decide
  | closed => decide
  | extendedHoursOpen => decide
  | extendedHoursClose => decide
  | extendedHoursCxls => decide
  | mocImbalance => decide
  | ccpDetermination => decide
  | priceMovementExtension => decide
  | closing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MarketState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MarketState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MarketState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MarketState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MarketState

/-- Bypass: one byte code -/
def Bypass.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Bypass where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ Bypass.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Bypass

def toByte : Bypass → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Bypass :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : Bypass :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Bypass) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Bypass) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Bypass × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Bypass) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Bypass) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Bypass

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x49, 0x42, 0x43, 0x44, 0x52, 0x56, 0x20]

inductive CrossType where
  | internal -- Internal
  | basis -- Basis
  | contingent -- Contingent
  | derivativeRelated -- Derivative Related
  | regular -- Regular
  | volumeWeightedAveragePrice -- Volume Weighted Average Price
  | default -- Default
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .internal => 0x49
  | .basis => 0x42
  | .contingent => 0x43
  | .derivativeRelated => 0x44
  | .regular => 0x52
  | .volumeWeightedAveragePrice => 0x56
  | .default => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x49 then .internal
  else if byte = 0x42 then .basis
  else if byte = 0x43 then .contingent
  else if byte = 0x44 then .derivativeRelated
  else if byte = 0x52 then .regular
  else if byte = 0x56 then .volumeWeightedAveragePrice
  else .default

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | internal => decide
  | basis => decide
  | contingent => decide
  | derivativeRelated => decide
  | regular => decide
  | volumeWeightedAveragePrice => decide
  | default => decide
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

/-- Settlement Terms: one byte code -/
def SettlementTerms.codes : List UInt8 :=
  [0x43, 0x4E, 0x4D, 0x54, 0x44, 0x20]

inductive SettlementTerms where
  | cash -- Cash
  | nn -- Nn
  | ms -- Ms
  | ct -- Ct
  | xalidSettlementDate -- Xalid Settlement Date
  | noSettlementTerms -- No Settlement Terms
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlementTerms.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlementTerms

def toByte : SettlementTerms → UInt8
  | .cash => 0x43
  | .nn => 0x4E
  | .ms => 0x4D
  | .ct => 0x54
  | .xalidSettlementDate => 0x44
  | .noSettlementTerms => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlementTerms :=
  if byte = 0x43 then .cash
  else if byte = 0x4E then .nn
  else if byte = 0x4D then .ms
  else if byte = 0x54 then .ct
  else if byte = 0x44 then .xalidSettlementDate
  else .noSettlementTerms

def ofByte (byte : UInt8) : SettlementTerms :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlementTerms) : ofByte value.toByte = value := by
  cases value with
  | cash => decide
  | nn => decide
  | ms => decide
  | ct => decide
  | xalidSettlementDate => decide
  | noSettlementTerms => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlementTerms) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlementTerms × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlementTerms) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlementTerms) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlementTerms

/-- Initiated By: one byte code -/
def InitiatedBy.codes : List UInt8 :=
  [0x42, 0x53, 0x43]

inductive InitiatedBy where
  | buySide -- Buy Side
  | sellSide -- Sell Side
  | bothSides -- Both Sides
  | unlisted (byte : { byte : UInt8 // byte ∉ InitiatedBy.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InitiatedBy

def toByte : InitiatedBy → UInt8
  | .buySide => 0x42
  | .sellSide => 0x53
  | .bothSides => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InitiatedBy :=
  if byte = 0x42 then .buySide
  else if byte = 0x53 then .sellSide
  else .bothSides

def ofByte (byte : UInt8) : InitiatedBy :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InitiatedBy) : ofByte value.toByte = value := by
  cases value with
  | buySide => decide
  | sellSide => decide
  | bothSides => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InitiatedBy) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InitiatedBy × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InitiatedBy) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InitiatedBy) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InitiatedBy

/-- Business Header: 9 bytes -/
structure BusinessHeader where
  msgVersion : BitVec 8
  sourceId : Alpha 1
  streamId : BitVec 16
  sequence0 : BitVec 8
  sequence1 : BitVec 32
  deriving DecidableEq, Repr

namespace BusinessHeader

def encode (message : BusinessHeader) : List UInt8 :=
  encodeUInt 1 message.msgVersion
    ++ (Alpha.encode message.sourceId
    ++ (encodeUIntLE 2 message.streamId
    ++ (encodeUIntLE 1 message.sequence0
    ++ (encodeUIntLE 4 message.sequence1))))

def decode (bytes : List UInt8) : Option (BusinessHeader × List UInt8) := do
  let (msgVersion, bytes) ← decodeUInt 1 bytes
  let (sourceId, bytes) ← Alpha.decode 1 bytes
  let (streamId, bytes) ← decodeUIntLE 2 bytes
  let (sequence0, bytes) ← decodeUIntLE 1 bytes
  let (sequence1, bytes) ← decodeUIntLE 4 bytes
  pure ({ msgVersion, sourceId, streamId, sequence0, sequence1 }, bytes)

@[simp] theorem encode_length (message : BusinessHeader) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BusinessHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BusinessHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BusinessHeader

/-- Symbol Status Message: 53 bytes -/
structure SymbolStatusMessage where
  symbol : Alpha 12
  stockGroup : BitVec 8
  listingMarket : ListingMarket
  productType : ProductType
  cusip : Alpha 12
  boardLot : BitVec 16
  currency : Currency
  faceValue : BitVec 64
  lastSale : BitVec 64
  minPoQty : BitVec 32
  stockState : Alpha 2
  testSymbol : TestSymbol
  deriving DecidableEq, Repr

namespace SymbolStatusMessage

def encode (message : SymbolStatusMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 1 message.stockGroup
    ++ (ListingMarket.encode message.listingMarket
    ++ (ProductType.encode message.productType
    ++ (Alpha.encode message.cusip
    ++ (encodeUIntLE 2 message.boardLot
    ++ (Currency.encode message.currency
    ++ (encodeUIntLE 8 message.faceValue
    ++ (encodeUIntLE 8 message.lastSale
    ++ (encodeUIntLE 4 message.minPoQty
    ++ (Alpha.encode message.stockState
    ++ (TestSymbol.encode message.testSymbol)))))))))))

def decode (bytes : List UInt8) : Option (SymbolStatusMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (stockGroup, bytes) ← decodeUIntLE 1 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (productType, bytes) ← ProductType.decode bytes
  let (cusip, bytes) ← Alpha.decode 12 bytes
  let (boardLot, bytes) ← decodeUIntLE 2 bytes
  let (currency, bytes) ← Currency.decode bytes
  let (faceValue, bytes) ← decodeUIntLE 8 bytes
  let (lastSale, bytes) ← decodeUIntLE 8 bytes
  let (minPoQty, bytes) ← decodeUIntLE 4 bytes
  let (stockState, bytes) ← Alpha.decode 2 bytes
  let (testSymbol, bytes) ← TestSymbol.decode bytes
  pure ({ symbol, stockGroup, listingMarket, productType, cusip, boardLot, currency, faceValue, lastSale, minPoQty, stockState, testSymbol }, bytes)

@[simp] theorem encode_length (message : SymbolStatusMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, ListingMarket.encode_length, ProductType.encode_length, Currency.encode_length, TestSymbol.encode_length]

theorem encode_length_pos (message : SymbolStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ProductType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Currency.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [TestSymbol.decode_encode, some_bind]
  rfl

end SymbolStatusMessage

/-- Order Book Message: 43 bytes -/
structure OrderBookMessage where
  symbol : Alpha 12
  brokerNumber : BitVec 16
  orderSide : OrderSide
  orderId : BitVec 64
  price : BitVec 64
  volume : BitVec 32
  priorityTimeStamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderBookMessage

def encode (message : OrderBookMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 2 message.brokerNumber
    ++ (OrderSide.encode message.orderSide
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 8 message.priorityTimeStamp))))))

def decode (bytes : List UInt8) : Option (OrderBookMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (brokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (priorityTimeStamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbol, brokerNumber, orderSide, orderId, price, volume, priorityTimeStamp }, bytes)

@[simp] theorem encode_length (message : OrderBookMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, OrderSide.encode_length]

theorem encode_length_pos (message : OrderBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderBookMessage

/-- Market State Update Message: 10 bytes -/
structure MarketStateUpdateMessage where
  marketState : MarketState
  stockGroup : BitVec 8
  tradingSystemTimeStamp : BitVec 64
  deriving DecidableEq, Repr

namespace MarketStateUpdateMessage

def encode (message : MarketStateUpdateMessage) : List UInt8 :=
  MarketState.encode message.marketState
    ++ (encodeUIntLE 1 message.stockGroup
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp))

def decode (bytes : List UInt8) : Option (MarketStateUpdateMessage × List UInt8) := do
  let (marketState, bytes) ← MarketState.decode bytes
  let (stockGroup, bytes) ← decodeUIntLE 1 bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ marketState, stockGroup, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : MarketStateUpdateMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, MarketState.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MarketStateUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketStateUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, MarketState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MarketStateUpdateMessage

/-- Order Booked Message: 51 bytes -/
structure OrderBookedMessage where
  symbol : Alpha 12
  brokerNumber : BitVec 16
  orderSide : OrderSide
  orderId : BitVec 64
  price : BitVec 64
  volume : BitVec 32
  priorityTimeStamp : BitVec 64
  tradingSystemTimeStamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderBookedMessage

def encode (message : OrderBookedMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 2 message.brokerNumber
    ++ (OrderSide.encode message.orderSide
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 8 message.priorityTimeStamp
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp)))))))

def decode (bytes : List UInt8) : Option (OrderBookedMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (brokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (priorityTimeStamp, bytes) ← decodeUIntLE 8 bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbol, brokerNumber, orderSide, orderId, price, volume, priorityTimeStamp, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : OrderBookedMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, OrderSide.encode_length]

theorem encode_length_pos (message : OrderBookedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
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

end OrderBookedMessage

/-- Order Cancelled Message: 31 bytes -/
structure OrderCancelledMessage where
  symbol : Alpha 12
  brokerNumber : BitVec 16
  orderSide : OrderSide
  orderId : BitVec 64
  tradingSystemTimeStamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelledMessage

def encode (message : OrderCancelledMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 2 message.brokerNumber
    ++ (OrderSide.encode message.orderSide
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp))))

def decode (bytes : List UInt8) : Option (OrderCancelledMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (brokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbol, brokerNumber, orderSide, orderId, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : OrderCancelledMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, OrderSide.encode_length]

theorem encode_length_pos (message : OrderCancelledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancelledMessage

/-- Order Price Time Assigned Message: 51 bytes -/
structure OrderPriceTimeAssignedMessage where
  symbol : Alpha 12
  brokerNumber : BitVec 16
  orderSide : OrderSide
  orderId : BitVec 64
  price : BitVec 64
  volume : BitVec 32
  priorityTimeStamp : BitVec 64
  tradingSystemTimeStamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderPriceTimeAssignedMessage

def encode (message : OrderPriceTimeAssignedMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 2 message.brokerNumber
    ++ (OrderSide.encode message.orderSide
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 8 message.priorityTimeStamp
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp)))))))

def decode (bytes : List UInt8) : Option (OrderPriceTimeAssignedMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (brokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (priorityTimeStamp, bytes) ← decodeUIntLE 8 bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbol, brokerNumber, orderSide, orderId, price, volume, priorityTimeStamp, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : OrderPriceTimeAssignedMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, OrderSide.encode_length]

theorem encode_length_pos (message : OrderPriceTimeAssignedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderPriceTimeAssignedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
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

end OrderPriceTimeAssignedMessage

/-- Stock Status Message: 62 bytes -/
structure StockStatusMessage where
  symbol : Alpha 12
  comment : Alpha 40
  stockState : Alpha 2
  tradingSystemTimeStamp : BitVec 64
  deriving DecidableEq, Repr

namespace StockStatusMessage

def encode (message : StockStatusMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (Alpha.encode message.comment
    ++ (Alpha.encode message.stockState
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp)))

def decode (bytes : List UInt8) : Option (StockStatusMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (comment, bytes) ← Alpha.decode 40 bytes
  let (stockState, bytes) ← Alpha.decode 2 bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbol, comment, stockState, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : StockStatusMessage) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : StockStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StockStatusMessage

/-- Trade Report Message: 71 bytes -/
structure TradeReportMessage where
  symbol : Alpha 12
  tradeNumber : BitVec 32
  price : BitVec 64
  volume : BitVec 32
  buyBrokerNumber : BitVec 16
  buyOrderId : BitVec 64
  buyDisplayVolume : BitVec 32
  sellBrokerNumber : BitVec 16
  sellOrderId : BitVec 64
  sellDisplayVolume : BitVec 32
  bypass : Bypass
  tradeTimeStamp : BitVec 32
  crossType : CrossType
  isDark : Alpha 1
  tradingSystemTimeStamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradeReportMessage

def encode (message : TradeReportMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.tradeNumber
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 2 message.buyBrokerNumber
    ++ (encodeUIntLE 8 message.buyOrderId
    ++ (encodeUIntLE 4 message.buyDisplayVolume
    ++ (encodeUIntLE 2 message.sellBrokerNumber
    ++ (encodeUIntLE 8 message.sellOrderId
    ++ (encodeUIntLE 4 message.sellDisplayVolume
    ++ (Bypass.encode message.bypass
    ++ (encodeUIntLE 4 message.tradeTimeStamp
    ++ (CrossType.encode message.crossType
    ++ (Alpha.encode message.isDark
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp))))))))))))))

def decode (bytes : List UInt8) : Option (TradeReportMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradeNumber, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (buyBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (buyOrderId, bytes) ← decodeUIntLE 8 bytes
  let (buyDisplayVolume, bytes) ← decodeUIntLE 4 bytes
  let (sellBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (sellOrderId, bytes) ← decodeUIntLE 8 bytes
  let (sellDisplayVolume, bytes) ← decodeUIntLE 4 bytes
  let (bypass, bytes) ← Bypass.decode bytes
  let (tradeTimeStamp, bytes) ← decodeUIntLE 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (isDark, bytes) ← Alpha.decode 1 bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbol, tradeNumber, price, volume, buyBrokerNumber, buyOrderId, buyDisplayVolume, sellBrokerNumber, sellOrderId, sellDisplayVolume, bypass, tradeTimeStamp, crossType, isDark, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : TradeReportMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, Bypass.encode_length, CrossType.encode_length]

theorem encode_length_pos (message : TradeReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Bypass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeReportMessage

/-- Trade Report Terms Message: 74 bytes -/
structure TradeReportTermsMessage where
  symbol : Alpha 12
  tradeNumber : BitVec 32
  price : BitVec 64
  volume : BitVec 32
  buyBrokerNumber : BitVec 16
  buyOrderId : BitVec 64
  buyDisplayVolume : BitVec 32
  sellBrokerNumber : BitVec 16
  sellOrderId : BitVec 64
  sellDisplayVolume : BitVec 32
  tradeTimeStamp : BitVec 32
  settlementTerms : SettlementTerms
  settlementDate : BitVec 32
  crossType : CrossType
  tradingSystemTimeStamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradeReportTermsMessage

def encode (message : TradeReportTermsMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.tradeNumber
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 2 message.buyBrokerNumber
    ++ (encodeUIntLE 8 message.buyOrderId
    ++ (encodeUIntLE 4 message.buyDisplayVolume
    ++ (encodeUIntLE 2 message.sellBrokerNumber
    ++ (encodeUIntLE 8 message.sellOrderId
    ++ (encodeUIntLE 4 message.sellDisplayVolume
    ++ (encodeUIntLE 4 message.tradeTimeStamp
    ++ (SettlementTerms.encode message.settlementTerms
    ++ (encodeUIntLE 4 message.settlementDate
    ++ (CrossType.encode message.crossType
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp))))))))))))))

def decode (bytes : List UInt8) : Option (TradeReportTermsMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradeNumber, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (buyBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (buyOrderId, bytes) ← decodeUIntLE 8 bytes
  let (buyDisplayVolume, bytes) ← decodeUIntLE 4 bytes
  let (sellBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (sellOrderId, bytes) ← decodeUIntLE 8 bytes
  let (sellDisplayVolume, bytes) ← decodeUIntLE 4 bytes
  let (tradeTimeStamp, bytes) ← decodeUIntLE 4 bytes
  let (settlementTerms, bytes) ← SettlementTerms.decode bytes
  let (settlementDate, bytes) ← decodeUIntLE 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbol, tradeNumber, price, volume, buyBrokerNumber, buyOrderId, buyDisplayVolume, sellBrokerNumber, sellOrderId, sellDisplayVolume, tradeTimeStamp, settlementTerms, settlementDate, crossType, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : TradeReportTermsMessage) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, SettlementTerms.encode_length, CrossType.encode_length]

theorem encode_length_pos (message : TradeReportTermsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReportTermsMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, SettlementTerms.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeReportTermsMessage

/-- Trade Cancelled Message: 24 bytes -/
structure TradeCancelledMessage where
  symbol : Alpha 12
  tradeNumber : BitVec 32
  tradingSystemTimeStamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCancelledMessage

def encode (message : TradeCancelledMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.tradeNumber
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp))

def decode (bytes : List UInt8) : Option (TradeCancelledMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradeNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbol, tradeNumber, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : TradeCancelledMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCancelledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCancelledMessage

/-- Trade Cancelled Terms Message: 24 bytes -/
structure TradeCancelledTermsMessage where
  symbol : Alpha 12
  tradeNumber : BitVec 32
  tradingSystemTimeStamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCancelledTermsMessage

def encode (message : TradeCancelledTermsMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.tradeNumber
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp))

def decode (bytes : List UInt8) : Option (TradeCancelledTermsMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradeNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbol, tradeNumber, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : TradeCancelledTermsMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCancelledTermsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelledTermsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCancelledTermsMessage

/-- Trade Correction Message: 52 bytes -/
structure TradeCorrectionMessage where
  symbol : Alpha 12
  tradeNumber : BitVec 32
  price : BitVec 64
  volume : BitVec 32
  buyBrokerNumber : BitVec 16
  sellBrokerNumber : BitVec 16
  initiatedBy : InitiatedBy
  origTradeNumber : BitVec 32
  bypass : Bypass
  tradeTimeStamp : BitVec 32
  crossType : CrossType
  isDark : Alpha 1
  tradingSystemTimeStamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCorrectionMessage

def encode (message : TradeCorrectionMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.tradeNumber
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 2 message.buyBrokerNumber
    ++ (encodeUIntLE 2 message.sellBrokerNumber
    ++ (InitiatedBy.encode message.initiatedBy
    ++ (encodeUIntLE 4 message.origTradeNumber
    ++ (Bypass.encode message.bypass
    ++ (encodeUIntLE 4 message.tradeTimeStamp
    ++ (CrossType.encode message.crossType
    ++ (Alpha.encode message.isDark
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp))))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradeNumber, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (buyBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (sellBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (initiatedBy, bytes) ← InitiatedBy.decode bytes
  let (origTradeNumber, bytes) ← decodeUIntLE 4 bytes
  let (bypass, bytes) ← Bypass.decode bytes
  let (tradeTimeStamp, bytes) ← decodeUIntLE 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (isDark, bytes) ← Alpha.decode 1 bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbol, tradeNumber, price, volume, buyBrokerNumber, sellBrokerNumber, initiatedBy, origTradeNumber, bypass, tradeTimeStamp, crossType, isDark, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, InitiatedBy.encode_length, Bypass.encode_length, CrossType.encode_length]

theorem encode_length_pos (message : TradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, InitiatedBy.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Bypass.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCorrectionMessage

/-- Trade Correction Terms Message: 55 bytes -/
structure TradeCorrectionTermsMessage where
  symbol : Alpha 12
  tradeNumber : BitVec 32
  price : BitVec 64
  volume : BitVec 32
  buyBrokerNumber : BitVec 16
  sellBrokerNumber : BitVec 16
  initiatedBy : InitiatedBy
  origTradeNumber : BitVec 32
  tradeTimeStamp : BitVec 32
  settlementTerms : SettlementTerms
  settlementDate : BitVec 32
  crossType : CrossType
  tradingSystemTimeStamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCorrectionTermsMessage

def encode (message : TradeCorrectionTermsMessage) : List UInt8 :=
  Alpha.encode message.symbol
    ++ (encodeUIntLE 4 message.tradeNumber
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.volume
    ++ (encodeUIntLE 2 message.buyBrokerNumber
    ++ (encodeUIntLE 2 message.sellBrokerNumber
    ++ (InitiatedBy.encode message.initiatedBy
    ++ (encodeUIntLE 4 message.origTradeNumber
    ++ (encodeUIntLE 4 message.tradeTimeStamp
    ++ (SettlementTerms.encode message.settlementTerms
    ++ (encodeUIntLE 4 message.settlementDate
    ++ (CrossType.encode message.crossType
    ++ (encodeUIntLE 8 message.tradingSystemTimeStamp))))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectionTermsMessage × List UInt8) := do
  let (symbol, bytes) ← Alpha.decode 12 bytes
  let (tradeNumber, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (volume, bytes) ← decodeUIntLE 4 bytes
  let (buyBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (sellBrokerNumber, bytes) ← decodeUIntLE 2 bytes
  let (initiatedBy, bytes) ← InitiatedBy.decode bytes
  let (origTradeNumber, bytes) ← decodeUIntLE 4 bytes
  let (tradeTimeStamp, bytes) ← decodeUIntLE 4 bytes
  let (settlementTerms, bytes) ← SettlementTerms.decode bytes
  let (settlementDate, bytes) ← decodeUIntLE 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (tradingSystemTimeStamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbol, tradeNumber, price, volume, buyBrokerNumber, sellBrokerNumber, initiatedBy, origTradeNumber, tradeTimeStamp, settlementTerms, settlementDate, crossType, tradingSystemTimeStamp }, bytes)

@[simp] theorem encode_length (message : TradeCorrectionTermsMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, InitiatedBy.encode_length, SettlementTerms.encode_length, CrossType.encode_length]

theorem encode_length_pos (message : TradeCorrectionTermsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectionTermsMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, InitiatedBy.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, SettlementTerms.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCorrectionTermsMessage

/-- Any Business Message, selected by Msg Type -/
inductive BusinessMessage where
  | symbolStatusMessage (message : SymbolStatusMessage) -- "J" 0x4A
  | orderBookMessage (message : OrderBookMessage) -- "G" 0x47
  | marketStateUpdateMessage (message : MarketStateUpdateMessage) -- "E" 0x45
  | orderBookedMessage (message : OrderBookedMessage) -- "P" 0x50
  | orderCancelledMessage (message : OrderCancelledMessage) -- "Q" 0x51
  | orderPriceTimeAssignedMessage (message : OrderPriceTimeAssignedMessage) -- "R" 0x52
  | stockStatusMessage (message : StockStatusMessage) -- "I" 0x49
  | tradeReportMessage (message : TradeReportMessage) -- "S" 0x53
  | tradeReportTermsMessage (message : TradeReportTermsMessage) -- "p" 0x70
  | tradeCancelledMessage (message : TradeCancelledMessage) -- "T" 0x54
  | tradeCancelledTermsMessage (message : TradeCancelledTermsMessage) -- "q" 0x71
  | tradeCorrectionMessage (message : TradeCorrectionMessage) -- "U" 0x55
  | tradeCorrectionTermsMessage (message : TradeCorrectionTermsMessage) -- "r" 0x72
  deriving DecidableEq, Repr

namespace BusinessMessage

/-- The Msg Type each message is sent under -/
def tag : BusinessMessage → BitVec 8
  | .symbolStatusMessage _ => 74
  | .orderBookMessage _ => 71
  | .marketStateUpdateMessage _ => 69
  | .orderBookedMessage _ => 80
  | .orderCancelledMessage _ => 81
  | .orderPriceTimeAssignedMessage _ => 82
  | .stockStatusMessage _ => 73
  | .tradeReportMessage _ => 83
  | .tradeReportTermsMessage _ => 112
  | .tradeCancelledMessage _ => 84
  | .tradeCancelledTermsMessage _ => 113
  | .tradeCorrectionMessage _ => 85
  | .tradeCorrectionTermsMessage _ => 114

def encode : BusinessMessage → List UInt8
  | .symbolStatusMessage message => SymbolStatusMessage.encode message
  | .orderBookMessage message => OrderBookMessage.encode message
  | .marketStateUpdateMessage message => MarketStateUpdateMessage.encode message
  | .orderBookedMessage message => OrderBookedMessage.encode message
  | .orderCancelledMessage message => OrderCancelledMessage.encode message
  | .orderPriceTimeAssignedMessage message => OrderPriceTimeAssignedMessage.encode message
  | .stockStatusMessage message => StockStatusMessage.encode message
  | .tradeReportMessage message => TradeReportMessage.encode message
  | .tradeReportTermsMessage message => TradeReportTermsMessage.encode message
  | .tradeCancelledMessage message => TradeCancelledMessage.encode message
  | .tradeCancelledTermsMessage message => TradeCancelledTermsMessage.encode message
  | .tradeCorrectionMessage message => TradeCorrectionMessage.encode message
  | .tradeCorrectionTermsMessage message => TradeCorrectionTermsMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : BusinessMessage) : (encode message).length ≤ 74 := by
  cases message with
  | symbolStatusMessage inner =>
    simp only [encode, SymbolStatusMessage.encode_length]
    omega
  | orderBookMessage inner =>
    simp only [encode, OrderBookMessage.encode_length]
    omega
  | marketStateUpdateMessage inner =>
    simp only [encode, MarketStateUpdateMessage.encode_length]
    omega
  | orderBookedMessage inner =>
    simp only [encode, OrderBookedMessage.encode_length]
    omega
  | orderCancelledMessage inner =>
    simp only [encode, OrderCancelledMessage.encode_length]
    omega
  | orderPriceTimeAssignedMessage inner =>
    simp only [encode, OrderPriceTimeAssignedMessage.encode_length]
    omega
  | stockStatusMessage inner =>
    simp only [encode, StockStatusMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [encode, TradeReportMessage.encode_length]
    omega
  | tradeReportTermsMessage inner =>
    simp only [encode, TradeReportTermsMessage.encode_length]
    omega
  | tradeCancelledMessage inner =>
    simp only [encode, TradeCancelledMessage.encode_length]
    omega
  | tradeCancelledTermsMessage inner =>
    simp only [encode, TradeCancelledTermsMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [encode, TradeCorrectionMessage.encode_length]
    omega
  | tradeCorrectionTermsMessage inner =>
    simp only [encode, TradeCorrectionTermsMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (BusinessMessage × List UInt8) :=
  if tag = 74 then (SymbolStatusMessage.decode bytes).map fun (message, rest) => (.symbolStatusMessage message, rest)
  else if tag = 71 then (OrderBookMessage.decode bytes).map fun (message, rest) => (.orderBookMessage message, rest)
  else if tag = 69 then (MarketStateUpdateMessage.decode bytes).map fun (message, rest) => (.marketStateUpdateMessage message, rest)
  else if tag = 80 then (OrderBookedMessage.decode bytes).map fun (message, rest) => (.orderBookedMessage message, rest)
  else if tag = 81 then (OrderCancelledMessage.decode bytes).map fun (message, rest) => (.orderCancelledMessage message, rest)
  else if tag = 82 then (OrderPriceTimeAssignedMessage.decode bytes).map fun (message, rest) => (.orderPriceTimeAssignedMessage message, rest)
  else if tag = 73 then (StockStatusMessage.decode bytes).map fun (message, rest) => (.stockStatusMessage message, rest)
  else if tag = 83 then (TradeReportMessage.decode bytes).map fun (message, rest) => (.tradeReportMessage message, rest)
  else if tag = 112 then (TradeReportTermsMessage.decode bytes).map fun (message, rest) => (.tradeReportTermsMessage message, rest)
  else if tag = 84 then (TradeCancelledMessage.decode bytes).map fun (message, rest) => (.tradeCancelledMessage message, rest)
  else if tag = 113 then (TradeCancelledTermsMessage.decode bytes).map fun (message, rest) => (.tradeCancelledTermsMessage message, rest)
  else if tag = 85 then (TradeCorrectionMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionMessage message, rest)
  else if tag = 114 then (TradeCorrectionTermsMessage.decode bytes).map fun (message, rest) => (.tradeCorrectionTermsMessage message, rest)
  else none

@[simp] theorem decode_encode (message : BusinessMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end BusinessMessage

/-- Body -/
structure Body where
  businessHeader : BusinessHeader
  businessMessage : BusinessMessage
  deriving DecidableEq, Repr

namespace Body

def encodeBody (message : Body) : List UInt8 :=
  encodeUInt 1 (BusinessMessage.tag message.businessMessage)
    ++ (BusinessHeader.encode message.businessHeader
    ++ (BusinessMessage.encode message.businessMessage))

def decodeBody (bytes : List UInt8) : Option (Body × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  let (businessHeader, bytes) ← BusinessHeader.decode bytes
  let (businessMessage, bytes) ← BusinessMessage.decode msgType bytes
  pure ({ businessHeader, businessMessage }, bytes)

theorem decodeBody_encodeBody (message : Body) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BusinessHeader.decode_encode, some_bind]
  dsimp only
  rw [BusinessMessage.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Body) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.businessMessage with
  | symbolStatusMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, SymbolStatusMessage.encode_length]
    omega
  | orderBookMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, OrderBookMessage.encode_length]
    omega
  | marketStateUpdateMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, MarketStateUpdateMessage.encode_length]
    omega
  | orderBookedMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, OrderBookedMessage.encode_length]
    omega
  | orderCancelledMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, OrderCancelledMessage.encode_length]
    omega
  | orderPriceTimeAssignedMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, OrderPriceTimeAssignedMessage.encode_length]
    omega
  | stockStatusMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, StockStatusMessage.encode_length]
    omega
  | tradeReportMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, TradeReportMessage.encode_length]
    omega
  | tradeReportTermsMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, TradeReportTermsMessage.encode_length]
    omega
  | tradeCancelledMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, TradeCancelledMessage.encode_length]
    omega
  | tradeCancelledTermsMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, TradeCancelledTermsMessage.encode_length]
    omega
  | tradeCorrectionMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, TradeCorrectionMessage.encode_length]
    omega
  | tradeCorrectionTermsMessage inner =>
    simp only [BusinessMessage.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BusinessHeader.encode_length, TradeCorrectionTermsMessage.encode_length]
    omega

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Body → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Body × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Body) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Body) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Body

/-- Packet -/
structure Packet where
  startOfFrame : BitVec 8
  protocolName : ProtocolName
  protocolVersion : Alpha 1
  sessionId : BitVec 32
  ackRequiredPossDup : AckRequiredPossDup
  body : Bounded 1 Body
  deriving DecidableEq, Repr

namespace Packet

def encodeBody (message : Packet) : List UInt8 :=
  encodeUIntLE 4 message.sessionId
    ++ (AckRequiredPossDup.encode message.ackRequiredPossDup
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.body.val.length)
    ++ (encodeMany Body.encode message.body.val)))

def decodeBody (startOfFrame : BitVec 8) (protocolName : ProtocolName) (protocolVersion : Alpha 1) (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (sessionId, bytes) ← decodeUIntLE 4 bytes
  let (ackRequiredPossDup, bytes) ← AckRequiredPossDup.decode bytes
  let (numBody, bytes) ← decodeUInt 1 bytes
  let (body_, bytes) ← decodeMany Body.decode numBody.toNat bytes
  if fits_body : body_.length < 256 ^ 1 then
    pure ({ startOfFrame, protocolName, protocolVersion, sessionId, ackRequiredPossDup, body := ⟨body_, fits_body⟩ }, bytes)
  else none

theorem decodeBody_encodeBody (message : Packet) (rest : List UInt8) :
    decodeBody message.startOfFrame message.protocolName message.protocolVersion (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, AckRequiredPossDup.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Body.encode Body.decode Body.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.body.length_lt]
  rfl

/-- Size rule: Message Length counts the bytes after it plus 10, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked; Start Of Frame, Protocol Name, Protocol Version are read ahead of it -/
def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 message.startOfFrame
    ++ (ProtocolName.encode message.protocolName
    ++ (Alpha.encode message.protocolVersion
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 10)) ++ encodeBody message)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (startOfFrame, bytes) ← decodeUInt 1 bytes
  let (protocolName, bytes) ← ProtocolName.decode bytes
  let (protocolVersion, bytes) ← Alpha.decode 1 bytes
  let (_, bytes) ← decodeUIntLE 2 bytes
  (decodeBody startOfFrame protocolName protocolVersion) bytes

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ProtocolName.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, ProtocolName.encode_length, Alpha.encode_length, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

end Packet

end Omi.TmxTsxalphaQuantumfeedlevel2XmtV22
