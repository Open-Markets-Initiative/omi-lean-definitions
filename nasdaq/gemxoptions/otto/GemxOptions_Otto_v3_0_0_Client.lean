import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Ouch to Trade Options v3.0.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Unsequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Note: Client Soup Bin Tcp Packet's Packet Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqGemxoptionsOttoOuchV300Client

/-- Alo Inst: one byte code -/
def AloInst.codes : List UInt8 :=
  [0x4E, 0x59]

inductive AloInst where
  | notAlo -- Not Alo
  | alo -- Alo
  | unlisted (byte : { byte : UInt8 // byte ∉ AloInst.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AloInst

def toByte : AloInst → UInt8
  | .notAlo => 0x4E
  | .alo => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AloInst :=
  if byte = 0x4E then .notAlo
  else .alo

def ofByte (byte : UInt8) : AloInst :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AloInst) : ofByte value.toByte = value := by
  cases value with
  | notAlo => decide
  | alo => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AloInst) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AloInst × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AloInst) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AloInst) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AloInst

/-- Iso: one byte code -/
def Iso.codes : List UInt8 :=
  [0x4E, 0x49]

inductive Iso where
  | notIso -- Not Iso
  | iso -- Iso
  | unlisted (byte : { byte : UInt8 // byte ∉ Iso.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Iso

def toByte : Iso → UInt8
  | .notIso => 0x4E
  | .iso => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Iso :=
  if byte = 0x4E then .notIso
  else .iso

def ofByte (byte : UInt8) : Iso :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Iso) : ofByte value.toByte = value := by
  cases value with
  | notIso => decide
  | iso => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Iso) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Iso × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Iso) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Iso) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Iso

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x4F, 0x4E]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | offer -- Offer
  | notDisclosed -- Not Disclosed
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .offer => 0x4F
  | .notDisclosed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x4F then .offer
  else .notDisclosed

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | offer => decide
  | notDisclosed => decide
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

/-- Order Type: one byte code -/
def OrderType.codes : List UInt8 :=
  [0x4C, 0x4D, 0x4E]

inductive OrderType where
  | limit -- Limit
  | market -- Market
  | notDisclosed -- Not Disclosed
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderType

def toByte : OrderType → UInt8
  | .limit => 0x4C
  | .market => 0x4D
  | .notDisclosed => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderType :=
  if byte = 0x4C then .limit
  else if byte = 0x4D then .market
  else .notDisclosed

def ofByte (byte : UInt8) : OrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderType) : ofByte value.toByte = value := by
  cases value with
  | limit => decide
  | market => decide
  | notDisclosed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderType

/-- Tif: one byte code -/
def Tif.codes : List UInt8 :=
  [0x44, 0x46, 0x49]

inductive Tif where
  | day -- Day
  | fok -- Fok
  | ioc -- Ioc
  | unlisted (byte : { byte : UInt8 // byte ∉ Tif.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Tif

def toByte : Tif → UInt8
  | .day => 0x44
  | .fok => 0x46
  | .ioc => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Tif :=
  if byte = 0x44 then .day
  else if byte = 0x46 then .fok
  else .ioc

def ofByte (byte : UInt8) : Tif :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Tif) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | fok => decide
  | ioc => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Tif) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Tif × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Tif) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Tif) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Tif

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x43, 0x46, 0x4D, 0x4F, 0x50, 0x42, 0x52, 0x20]

inductive Capacity where
  | customer -- Customer
  | firm -- Firm
  | marketMaker -- Market Maker
  | otherExchangeRegisteredMarketMaker -- Other Exchange Registered Market Maker
  | professionalCustomer -- Professional Customer
  | brokerDealer -- Broker Dealer
  | retail -- Retail
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .customer => 0x43
  | .firm => 0x46
  | .marketMaker => 0x4D
  | .otherExchangeRegisteredMarketMaker => 0x4F
  | .professionalCustomer => 0x50
  | .brokerDealer => 0x42
  | .retail => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x43 then .customer
  else if byte = 0x46 then .firm
  else if byte = 0x4D then .marketMaker
  else if byte = 0x4F then .otherExchangeRegisteredMarketMaker
  else if byte = 0x50 then .professionalCustomer
  else if byte = 0x42 then .brokerDealer
  else if byte = 0x52 then .retail
  else .notApplicable

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | firm => decide
  | marketMaker => decide
  | otherExchangeRegisteredMarketMaker => decide
  | professionalCustomer => decide
  | brokerDealer => decide
  | retail => decide
  | notApplicable => decide
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

/-- Auction Type: one byte code -/
def AuctionType.codes : List UInt8 :=
  [0x42, 0x46, 0x4F, 0x50, 0x48, 0x53, 0x4E]

inductive AuctionType where
  | blockOrderAuction -- Block Order Auction
  | simpleExposureOrder -- Simple Exposure Order
  | openingAuction -- Opening Auction
  | pimPixlAuction -- Pim Pixl Auction
  | facilitationAuction -- Facilitation Auction
  | solicitationAuction -- Solicitation Auction
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ AuctionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AuctionType

def toByte : AuctionType → UInt8
  | .blockOrderAuction => 0x42
  | .simpleExposureOrder => 0x46
  | .openingAuction => 0x4F
  | .pimPixlAuction => 0x50
  | .facilitationAuction => 0x48
  | .solicitationAuction => 0x53
  | .none_ => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AuctionType :=
  if byte = 0x42 then .blockOrderAuction
  else if byte = 0x46 then .simpleExposureOrder
  else if byte = 0x4F then .openingAuction
  else if byte = 0x50 then .pimPixlAuction
  else if byte = 0x48 then .facilitationAuction
  else if byte = 0x53 then .solicitationAuction
  else .none_

def ofByte (byte : UInt8) : AuctionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AuctionType) : ofByte value.toByte = value := by
  cases value with
  | blockOrderAuction => decide
  | simpleExposureOrder => decide
  | openingAuction => decide
  | pimPixlAuction => decide
  | facilitationAuction => decide
  | solicitationAuction => decide
  | none_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AuctionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AuctionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AuctionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AuctionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AuctionType

/-- Price Protection: one byte code -/
def PriceProtection.codes : List UInt8 :=
  [0x4C, 0x4E]

inductive PriceProtection where
  | local_ -- Local
  | national -- National
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceProtection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceProtection

def toByte : PriceProtection → UInt8
  | .local_ => 0x4C
  | .national => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceProtection :=
  if byte = 0x4C then .local_
  else .national

def ofByte (byte : UInt8) : PriceProtection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceProtection) : ofByte value.toByte = value := by
  cases value with
  | local_ => decide
  | national => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceProtection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceProtection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceProtection) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceProtection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceProtection

/-- Display When: one byte code -/
def DisplayWhen.codes : List UInt8 :=
  [0x49, 0x45, 0x4E]

inductive DisplayWhen where
  | immediate -- Immediate
  | exhaust -- Exhaust
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ DisplayWhen.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DisplayWhen

def toByte : DisplayWhen → UInt8
  | .immediate => 0x49
  | .exhaust => 0x45
  | .notApplicable => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DisplayWhen :=
  if byte = 0x49 then .immediate
  else if byte = 0x45 then .exhaust
  else .notApplicable

def ofByte (byte : UInt8) : DisplayWhen :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DisplayWhen) : ofByte value.toByte = value := by
  cases value with
  | immediate => decide
  | exhaust => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DisplayWhen) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DisplayWhen × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DisplayWhen) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DisplayWhen) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DisplayWhen

/-- Display Method: one byte code -/
def DisplayMethod.codes : List UInt8 :=
  [0x49, 0x52, 0x4E]

inductive DisplayMethod where
  | initial -- Initial
  | random -- Random
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ DisplayMethod.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DisplayMethod

def toByte : DisplayMethod → UInt8
  | .initial => 0x49
  | .random => 0x52
  | .none_ => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DisplayMethod :=
  if byte = 0x49 then .initial
  else if byte = 0x52 then .random
  else .none_

def ofByte (byte : UInt8) : DisplayMethod :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DisplayMethod) : ofByte value.toByte = value := by
  cases value with
  | initial => decide
  | random => decide
  | none_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DisplayMethod) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DisplayMethod × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DisplayMethod) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DisplayMethod) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DisplayMethod

/-- Stock Leg Short Sale: one byte code -/
def StockLegShortSale.codes : List UInt8 :=
  [0x4E, 0x48, 0x45]

inductive StockLegShortSale where
  | notApplicable -- Not Applicable
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ StockLegShortSale.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StockLegShortSale

def toByte : StockLegShortSale → UInt8
  | .notApplicable => 0x4E
  | .sellShort => 0x48
  | .sellShortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StockLegShortSale :=
  if byte = 0x4E then .notApplicable
  else if byte = 0x48 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : StockLegShortSale :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StockLegShortSale) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | sellShort => decide
  | sellShortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StockLegShortSale) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StockLegShortSale × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StockLegShortSale) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StockLegShortSale) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StockLegShortSale

/-- Stock Capacity: one byte code -/
def StockCapacity.codes : List UInt8 :=
  [0x50, 0x41, 0x52, 0x20]

inductive StockCapacity where
  | principal -- Principal
  | agency -- Agency
  | risklessPrincipal -- Riskless Principal
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ StockCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StockCapacity

def toByte : StockCapacity → UInt8
  | .principal => 0x50
  | .agency => 0x41
  | .risklessPrincipal => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StockCapacity :=
  if byte = 0x50 then .principal
  else if byte = 0x41 then .agency
  else if byte = 0x52 then .risklessPrincipal
  else .notApplicable

def ofByte (byte : UInt8) : StockCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StockCapacity) : ofByte value.toByte = value := by
  cases value with
  | principal => decide
  | agency => decide
  | risklessPrincipal => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StockCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StockCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StockCapacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StockCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StockCapacity

/-- Instrument Type: one byte code -/
def InstrumentType.codes : List UInt8 :=
  [0x41, 0x4F]

inductive InstrumentType where
  | all -- All
  | simpleInstrument -- Simple Instrument
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentType

def toByte : InstrumentType → UInt8
  | .all => 0x41
  | .simpleInstrument => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentType :=
  if byte = 0x41 then .all
  else .simpleInstrument

def ofByte (byte : UInt8) : InstrumentType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentType) : ofByte value.toByte = value := by
  cases value with
  | all => decide
  | simpleInstrument => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentType

/-- Scope: one byte code -/
def Scope.codes : List UInt8 :=
  [0x50, 0x49, 0x46]

inductive Scope where
  | product -- Product
  | instrument -- Instrument
  | firm -- Firm
  | unlisted (byte : { byte : UInt8 // byte ∉ Scope.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Scope

def toByte : Scope → UInt8
  | .product => 0x50
  | .instrument => 0x49
  | .firm => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Scope :=
  if byte = 0x50 then .product
  else if byte = 0x49 then .instrument
  else .firm

def ofByte (byte : UInt8) : Scope :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Scope) : ofByte value.toByte = value := by
  cases value with
  | product => decide
  | instrument => decide
  | firm => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Scope) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Scope × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Scope) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Scope) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Scope

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x41, 0x51, 0x43]

inductive CrossType where
  | auction -- Auction
  | qcc -- Qcc
  | ccc -- Ccc
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .auction => 0x41
  | .qcc => 0x51
  | .ccc => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x41 then .auction
  else if byte = 0x51 then .qcc
  else .ccc

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | auction => decide
  | qcc => decide
  | ccc => decide
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

/-- Primary Capacity: one byte code -/
def PrimaryCapacity.codes : List UInt8 :=
  [0x43, 0x46, 0x4D, 0x4F, 0x50, 0x42, 0x52, 0x20]

inductive PrimaryCapacity where
  | customer -- Customer
  | firm -- Firm
  | marketMaker -- Market Maker
  | otherExchangeRegisteredMarketMaker -- Other Exchange Registered Market Maker
  | professionalCustomer -- Professional Customer
  | brokerDealer -- Broker Dealer
  | retail -- Retail
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryCapacity

def toByte : PrimaryCapacity → UInt8
  | .customer => 0x43
  | .firm => 0x46
  | .marketMaker => 0x4D
  | .otherExchangeRegisteredMarketMaker => 0x4F
  | .professionalCustomer => 0x50
  | .brokerDealer => 0x42
  | .retail => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryCapacity :=
  if byte = 0x43 then .customer
  else if byte = 0x46 then .firm
  else if byte = 0x4D then .marketMaker
  else if byte = 0x4F then .otherExchangeRegisteredMarketMaker
  else if byte = 0x50 then .professionalCustomer
  else if byte = 0x42 then .brokerDealer
  else if byte = 0x52 then .retail
  else .notApplicable

def ofByte (byte : UInt8) : PrimaryCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryCapacity) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | firm => decide
  | marketMaker => decide
  | otherExchangeRegisteredMarketMaker => decide
  | professionalCustomer => decide
  | brokerDealer => decide
  | retail => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrimaryCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryCapacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrimaryCapacity

/-- Primary Stock Leg Short Sale: one byte code -/
def PrimaryStockLegShortSale.codes : List UInt8 :=
  [0x4E, 0x48, 0x45]

inductive PrimaryStockLegShortSale where
  | notApplicable -- Not Applicable
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryStockLegShortSale.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryStockLegShortSale

def toByte : PrimaryStockLegShortSale → UInt8
  | .notApplicable => 0x4E
  | .sellShort => 0x48
  | .sellShortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryStockLegShortSale :=
  if byte = 0x4E then .notApplicable
  else if byte = 0x48 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : PrimaryStockLegShortSale :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryStockLegShortSale) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | sellShort => decide
  | sellShortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrimaryStockLegShortSale) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryStockLegShortSale × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryStockLegShortSale) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryStockLegShortSale) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrimaryStockLegShortSale

/-- Primary Stock Capacity: one byte code -/
def PrimaryStockCapacity.codes : List UInt8 :=
  [0x50, 0x41, 0x52, 0x20]

inductive PrimaryStockCapacity where
  | principal -- Principal
  | agency -- Agency
  | risklessPrincipal -- Riskless Principal
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryStockCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryStockCapacity

def toByte : PrimaryStockCapacity → UInt8
  | .principal => 0x50
  | .agency => 0x41
  | .risklessPrincipal => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryStockCapacity :=
  if byte = 0x50 then .principal
  else if byte = 0x41 then .agency
  else if byte = 0x52 then .risklessPrincipal
  else .notApplicable

def ofByte (byte : UInt8) : PrimaryStockCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryStockCapacity) : ofByte value.toByte = value := by
  cases value with
  | principal => decide
  | agency => decide
  | risklessPrincipal => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrimaryStockCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryStockCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryStockCapacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryStockCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrimaryStockCapacity

/-- Contra Order Type: one byte code -/
def ContraOrderType.codes : List UInt8 :=
  [0x4C, 0x4D]

inductive ContraOrderType where
  | limit -- Limit
  | market -- Market
  | unlisted (byte : { byte : UInt8 // byte ∉ ContraOrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContraOrderType

def toByte : ContraOrderType → UInt8
  | .limit => 0x4C
  | .market => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContraOrderType :=
  if byte = 0x4C then .limit
  else .market

def ofByte (byte : UInt8) : ContraOrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContraOrderType) : ofByte value.toByte = value := by
  cases value with
  | limit => decide
  | market => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContraOrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContraOrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContraOrderType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ContraOrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContraOrderType

/-- Contra Capacity: one byte code -/
def ContraCapacity.codes : List UInt8 :=
  [0x43, 0x46, 0x4D, 0x4F, 0x50, 0x42, 0x52, 0x20]

inductive ContraCapacity where
  | customer -- Customer
  | firm -- Firm
  | marketMaker -- Market Maker
  | otherExchangeRegisteredMarketMaker -- Other Exchange Registered Market Maker
  | professionalCustomer -- Professional Customer
  | brokerDealer -- Broker Dealer
  | retail -- Retail
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ ContraCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContraCapacity

def toByte : ContraCapacity → UInt8
  | .customer => 0x43
  | .firm => 0x46
  | .marketMaker => 0x4D
  | .otherExchangeRegisteredMarketMaker => 0x4F
  | .professionalCustomer => 0x50
  | .brokerDealer => 0x42
  | .retail => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContraCapacity :=
  if byte = 0x43 then .customer
  else if byte = 0x46 then .firm
  else if byte = 0x4D then .marketMaker
  else if byte = 0x4F then .otherExchangeRegisteredMarketMaker
  else if byte = 0x50 then .professionalCustomer
  else if byte = 0x42 then .brokerDealer
  else if byte = 0x52 then .retail
  else .notApplicable

def ofByte (byte : UInt8) : ContraCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContraCapacity) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | firm => decide
  | marketMaker => decide
  | otherExchangeRegisteredMarketMaker => decide
  | professionalCustomer => decide
  | brokerDealer => decide
  | retail => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContraCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContraCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContraCapacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ContraCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContraCapacity

/-- Contra Stock Leg Short Sale: one byte code -/
def ContraStockLegShortSale.codes : List UInt8 :=
  [0x4E, 0x48, 0x45]

inductive ContraStockLegShortSale where
  | notApplicable -- Not Applicable
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ ContraStockLegShortSale.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContraStockLegShortSale

def toByte : ContraStockLegShortSale → UInt8
  | .notApplicable => 0x4E
  | .sellShort => 0x48
  | .sellShortExempt => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContraStockLegShortSale :=
  if byte = 0x4E then .notApplicable
  else if byte = 0x48 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : ContraStockLegShortSale :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContraStockLegShortSale) : ofByte value.toByte = value := by
  cases value with
  | notApplicable => decide
  | sellShort => decide
  | sellShortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContraStockLegShortSale) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContraStockLegShortSale × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContraStockLegShortSale) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ContraStockLegShortSale) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContraStockLegShortSale

/-- Contra Stock Capacity: one byte code -/
def ContraStockCapacity.codes : List UInt8 :=
  [0x50, 0x41, 0x52, 0x20]

inductive ContraStockCapacity where
  | principal -- Principal
  | agency -- Agency
  | risklessPrincipal -- Riskless Principal
  | notApplicable -- Not Applicable
  | unlisted (byte : { byte : UInt8 // byte ∉ ContraStockCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ContraStockCapacity

def toByte : ContraStockCapacity → UInt8
  | .principal => 0x50
  | .agency => 0x41
  | .risklessPrincipal => 0x52
  | .notApplicable => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ContraStockCapacity :=
  if byte = 0x50 then .principal
  else if byte = 0x41 then .agency
  else if byte = 0x52 then .risklessPrincipal
  else .notApplicable

def ofByte (byte : UInt8) : ContraStockCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ContraStockCapacity) : ofByte value.toByte = value := by
  cases value with
  | principal => decide
  | agency => decide
  | risklessPrincipal => decide
  | notApplicable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ContraStockCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ContraStockCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ContraStockCapacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ContraStockCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ContraStockCapacity

/-- Open Close: one byte code -/
def OpenClose.codes : List UInt8 :=
  [0x4F, 0x43, 0x20]

inductive OpenClose where
  | open_ -- Open
  | closed -- Closed
  | carryForward -- Carry Forward
  | unlisted (byte : { byte : UInt8 // byte ∉ OpenClose.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OpenClose

def toByte : OpenClose → UInt8
  | .open_ => 0x4F
  | .closed => 0x43
  | .carryForward => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OpenClose :=
  if byte = 0x4F then .open_
  else if byte = 0x43 then .closed
  else .carryForward

def ofByte (byte : UInt8) : OpenClose :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OpenClose) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | closed => decide
  | carryForward => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OpenClose) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OpenClose × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OpenClose) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OpenClose) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OpenClose

/-- Kill Action: one byte code -/
def KillAction.codes : List UInt8 :=
  [0x41, 0x52, 0x42]

inductive KillAction where
  | blockAndDelete -- Block And Delete
  | blockRemoved -- Block Removed
  | block -- Block
  | unlisted (byte : { byte : UInt8 // byte ∉ KillAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace KillAction

def toByte : KillAction → UInt8
  | .blockAndDelete => 0x41
  | .blockRemoved => 0x52
  | .block => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : KillAction :=
  if byte = 0x41 then .blockAndDelete
  else if byte = 0x52 then .blockRemoved
  else .block

def ofByte (byte : UInt8) : KillAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : KillAction) : ofByte value.toByte = value := by
  cases value with
  | blockAndDelete => decide
  | blockRemoved => decide
  | block => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : KillAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (KillAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : KillAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : KillAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end KillAction

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  debugText : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.debugText

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (debugText, bytes) ← Alpha.decode 1 bytes
  pure ({ debugText }, bytes)

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

end LoginRequestPacket

/-- Flex Leg Prices: 16 bytes -/
structure FlexLegPrices where
  legPrices : BitVec 64
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace FlexLegPrices

def encode (message : FlexLegPrices) : List UInt8 :=
  encodeUInt 8 message.legPrices
    ++ (Alpha.encode message.reserved8)

def decode (bytes : List UInt8) : Option (FlexLegPrices × List UInt8) := do
  let (legPrices, bytes) ← decodeUInt 8 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ legPrices, reserved8 }, bytes)

@[simp] theorem encode_length (message : FlexLegPrices) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : FlexLegPrices) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FlexLegPrices) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FlexLegPrices

/-- New Order Long Form Message -/
structure NewOrderLongFormMessage where
  firmId : Alpha 4
  instrumentId : BitVec 32
  clOrdId : Alpha 16
  cmta : BitVec 32
  clearingAccount : Alpha 4
  occAccount : BitVec 32
  custAcct : Alpha 10
  preferredParty : Alpha 3
  aloInst : AloInst
  iso : Iso
  side : Side
  orderType : OrderType
  price : BitVec 64
  quantity : BitVec 32
  minQty : BitVec 32
  tif : Tif
  capacity : Capacity
  auctionType : AuctionType
  auctionId : BitVec 32
  auctionDuration : BitVec 32
  disclosureMask : BitVec 8
  priceProtection : PriceProtection
  displayQty : BitVec 16
  displayWhen : DisplayWhen
  displayMethod : DisplayMethod
  displayLowQty : BitVec 16
  displayHighQty : BitVec 16
  positionEffectMask : BitVec 16
  stockLegShortSale : StockLegShortSale
  stockLegMpid : Alpha 4
  stockCapacity : StockCapacity
  reserved9 : Alpha 9
  flexLegPrices : Bounded 1 FlexLegPrices
  deriving DecidableEq, Repr

namespace NewOrderLongFormMessage

def encode (message : NewOrderLongFormMessage) : List UInt8 :=
  Alpha.encode message.firmId
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.clOrdId
    ++ (encodeUInt 4 message.cmta
    ++ (Alpha.encode message.clearingAccount
    ++ (encodeUInt 4 message.occAccount
    ++ (Alpha.encode message.custAcct
    ++ (Alpha.encode message.preferredParty
    ++ (AloInst.encode message.aloInst
    ++ (Iso.encode message.iso
    ++ (Side.encode message.side
    ++ (OrderType.encode message.orderType
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.minQty
    ++ (Tif.encode message.tif
    ++ (Capacity.encode message.capacity
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.auctionId
    ++ (encodeUInt 4 message.auctionDuration
    ++ (encodeUInt 1 message.disclosureMask
    ++ (PriceProtection.encode message.priceProtection
    ++ (encodeUInt 2 message.displayQty
    ++ (DisplayWhen.encode message.displayWhen
    ++ (DisplayMethod.encode message.displayMethod
    ++ (encodeUInt 2 message.displayLowQty
    ++ (encodeUInt 2 message.displayHighQty
    ++ (encodeUInt 2 message.positionEffectMask
    ++ (StockLegShortSale.encode message.stockLegShortSale
    ++ (Alpha.encode message.stockLegMpid
    ++ (StockCapacity.encode message.stockCapacity
    ++ (Alpha.encode message.reserved9
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.flexLegPrices.val.length)
    ++ (encodeMany FlexLegPrices.encode message.flexLegPrices.val)))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderLongFormMessage × List UInt8) := do
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (cmta, bytes) ← decodeUInt 4 bytes
  let (clearingAccount, bytes) ← Alpha.decode 4 bytes
  let (occAccount, bytes) ← decodeUInt 4 bytes
  let (custAcct, bytes) ← Alpha.decode 10 bytes
  let (preferredParty, bytes) ← Alpha.decode 3 bytes
  let (aloInst, bytes) ← AloInst.decode bytes
  let (iso_, bytes) ← Iso.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (minQty, bytes) ← decodeUInt 4 bytes
  let (tif, bytes) ← Tif.decode bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (auctionDuration, bytes) ← decodeUInt 4 bytes
  let (disclosureMask, bytes) ← decodeUInt 1 bytes
  let (priceProtection, bytes) ← PriceProtection.decode bytes
  let (displayQty, bytes) ← decodeUInt 2 bytes
  let (displayWhen, bytes) ← DisplayWhen.decode bytes
  let (displayMethod, bytes) ← DisplayMethod.decode bytes
  let (displayLowQty, bytes) ← decodeUInt 2 bytes
  let (displayHighQty, bytes) ← decodeUInt 2 bytes
  let (positionEffectMask, bytes) ← decodeUInt 2 bytes
  let (stockLegShortSale, bytes) ← StockLegShortSale.decode bytes
  let (stockLegMpid, bytes) ← Alpha.decode 4 bytes
  let (stockCapacity, bytes) ← StockCapacity.decode bytes
  let (reserved9, bytes) ← Alpha.decode 9 bytes
  let (numberOfFlexLegs, bytes) ← decodeUInt 1 bytes
  let (flexLegPrices_, bytes) ← decodeMany FlexLegPrices.decode numberOfFlexLegs.toNat bytes
  if fits_flexLegPrices : flexLegPrices_.length < 256 ^ 1 then
    pure ({ firmId, instrumentId, clOrdId, cmta, clearingAccount, occAccount, custAcct, preferredParty, aloInst, iso := iso_, side, orderType, price, quantity, minQty, tif, capacity, auctionType, auctionId, auctionDuration, disclosureMask, priceProtection, displayQty, displayWhen, displayMethod, displayLowQty, displayHighQty, positionEffectMask, stockLegShortSale, stockLegMpid, stockCapacity, reserved9, flexLegPrices := ⟨flexLegPrices_, fits_flexLegPrices⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewOrderLongFormMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderLongFormMessage) : (encode message).length ≤ 4188 := by
  have bound_flexLegPrices := message.flexLegPrices.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, AloInst.encode_length, Iso.encode_length, Side.encode_length, OrderType.encode_length, Tif.encode_length, Capacity.encode_length, AuctionType.encode_length, PriceProtection.encode_length, DisplayWhen.encode_length, DisplayMethod.encode_length, StockLegShortSale.encode_length, StockCapacity.encode_length, encodeMany_length_const FlexLegPrices.encode 16 FlexLegPrices.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderLongFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AloInst.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Iso.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Tif.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PriceProtection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, DisplayWhen.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DisplayMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, StockLegShortSale.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, StockCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 FlexLegPrices.encode FlexLegPrices.decode FlexLegPrices.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.flexLegPrices.length_lt]
  rfl

end NewOrderLongFormMessage

/-- New Order Short Form Message: 49 bytes -/
structure NewOrderShortFormMessage where
  firmId : Alpha 4
  instrumentId : BitVec 32
  clOrdId : Alpha 16
  aloInst : AloInst
  iso : Iso
  side : Side
  orderType : OrderType
  price : BitVec 64
  quantityShort : BitVec 16
  tif : Tif
  capacity : Capacity
  auctionType : AuctionType
  auctionId : BitVec 32
  priceProtection : PriceProtection
  positionEffectMask : BitVec 16
  stockCapacity : StockCapacity
  deriving DecidableEq, Repr

namespace NewOrderShortFormMessage

def encode (message : NewOrderShortFormMessage) : List UInt8 :=
  Alpha.encode message.firmId
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.clOrdId
    ++ (AloInst.encode message.aloInst
    ++ (Iso.encode message.iso
    ++ (Side.encode message.side
    ++ (OrderType.encode message.orderType
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 2 message.quantityShort
    ++ (Tif.encode message.tif
    ++ (Capacity.encode message.capacity
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 4 message.auctionId
    ++ (PriceProtection.encode message.priceProtection
    ++ (encodeUInt 2 message.positionEffectMask
    ++ (StockCapacity.encode message.stockCapacity)))))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderShortFormMessage × List UInt8) := do
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (aloInst, bytes) ← AloInst.decode bytes
  let (iso_, bytes) ← Iso.decode bytes
  let (side, bytes) ← Side.decode bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (quantityShort, bytes) ← decodeUInt 2 bytes
  let (tif, bytes) ← Tif.decode bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (auctionId, bytes) ← decodeUInt 4 bytes
  let (priceProtection, bytes) ← PriceProtection.decode bytes
  let (positionEffectMask, bytes) ← decodeUInt 2 bytes
  let (stockCapacity, bytes) ← StockCapacity.decode bytes
  pure ({ firmId, instrumentId, clOrdId, aloInst, iso := iso_, side, orderType, price, quantityShort, tif, capacity, auctionType, auctionId, priceProtection, positionEffectMask, stockCapacity }, bytes)

@[simp] theorem encode_length (message : NewOrderShortFormMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, AloInst.encode_length, Iso.encode_length, Side.encode_length, OrderType.encode_length, Tif.encode_length, Capacity.encode_length, AuctionType.encode_length, PriceProtection.encode_length, StockCapacity.encode_length]

theorem encode_length_pos (message : NewOrderShortFormMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderShortFormMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AloInst.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Iso.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Tif.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PriceProtection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [StockCapacity.decode_encode, some_bind]
  rfl

end NewOrderShortFormMessage

/-- Replace Order Message: 61 bytes -/
structure ReplaceOrderMessage where
  firmId : Alpha 4
  origClOrdId : Alpha 16
  clOrdId : Alpha 16
  quantity : BitVec 32
  orderType : OrderType
  price : BitVec 64
  tif : Tif
  custAcct : Alpha 10
  priceProtection : PriceProtection
  deriving DecidableEq, Repr

namespace ReplaceOrderMessage

def encode (message : ReplaceOrderMessage) : List UInt8 :=
  Alpha.encode message.firmId
    ++ (Alpha.encode message.origClOrdId
    ++ (Alpha.encode message.clOrdId
    ++ (encodeUInt 4 message.quantity
    ++ (OrderType.encode message.orderType
    ++ (encodeUInt 8 message.price
    ++ (Tif.encode message.tif
    ++ (Alpha.encode message.custAcct
    ++ (PriceProtection.encode message.priceProtection))))))))

def decode (bytes : List UInt8) : Option (ReplaceOrderMessage × List UInt8) := do
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (origClOrdId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (orderType, bytes) ← OrderType.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (tif, bytes) ← Tif.decode bytes
  let (custAcct, bytes) ← Alpha.decode 10 bytes
  let (priceProtection, bytes) ← PriceProtection.decode bytes
  pure ({ firmId, origClOrdId, clOrdId, quantity, orderType, price, tif, custAcct, priceProtection }, bytes)

@[simp] theorem encode_length (message : ReplaceOrderMessage) : (encode message).length = 61 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, OrderType.encode_length, Tif.encode_length, PriceProtection.encode_length]

theorem encode_length_pos (message : ReplaceOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplaceOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Tif.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PriceProtection.decode_encode, some_bind]
  rfl

end ReplaceOrderMessage

/-- Cancel Order Message: 20 bytes -/
structure CancelOrderMessage where
  firmId : Alpha 4
  clOrdId : Alpha 16
  deriving DecidableEq, Repr

namespace CancelOrderMessage

def encode (message : CancelOrderMessage) : List UInt8 :=
  Alpha.encode message.firmId
    ++ (Alpha.encode message.clOrdId)

def decode (bytes : List UInt8) : Option (CancelOrderMessage × List UInt8) := do
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  pure ({ firmId, clOrdId }, bytes)

@[simp] theorem encode_length (message : CancelOrderMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : CancelOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelOrderMessage

/-- Mass Cancel Message: 41 bytes -/
structure MassCancelMessage where
  firmId : Alpha 4
  clRequestId : Alpha 16
  instrumentType : InstrumentType
  scope : Scope
  productId : BitVec 16
  instrumentId : BitVec 32
  underlyingSymbol : Alpha 13
  deriving DecidableEq, Repr

namespace MassCancelMessage

def encode (message : MassCancelMessage) : List UInt8 :=
  Alpha.encode message.firmId
    ++ (Alpha.encode message.clRequestId
    ++ (InstrumentType.encode message.instrumentType
    ++ (Scope.encode message.scope
    ++ (encodeUInt 2 message.productId
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.underlyingSymbol))))))

def decode (bytes : List UInt8) : Option (MassCancelMessage × List UInt8) := do
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (clRequestId, bytes) ← Alpha.decode 16 bytes
  let (instrumentType, bytes) ← InstrumentType.decode bytes
  let (scope, bytes) ← Scope.decode bytes
  let (productId, bytes) ← decodeUInt 2 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  pure ({ firmId, clRequestId, instrumentType, scope, productId, instrumentId, underlyingSymbol }, bytes)

@[simp] theorem encode_length (message : MassCancelMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, InstrumentType.encode_length, Scope.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Scope.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MassCancelMessage

/-- New Cross Order Message -/
structure NewCrossOrderMessage where
  firmId : Alpha 4
  instrumentId : BitVec 32
  crossType : CrossType
  auctionType : AuctionType
  auctionAllocPct : BitVec 8
  side : Side
  iso : Iso
  priceProtection : PriceProtection
  effectiveTime : BitVec 64
  disclosureMask : BitVec 8
  auctionDuration : BitVec 32
  reserved9 : Alpha 9
  primaryClOrdId : Alpha 16
  primaryCmta : BitVec 32
  primaryClearingAccount : Alpha 4
  primaryOccAccount : BitVec 32
  primaryCustAcct : Alpha 10
  primaryPrice : BitVec 64
  primaryQuantity : BitVec 32
  primaryCapacity : PrimaryCapacity
  primaryPositionEffectMask : BitVec 16
  primaryStockLegShortSale : PrimaryStockLegShortSale
  primaryStockLegMpid : Alpha 4
  primaryStockCapacity : PrimaryStockCapacity
  contraClOrdId : Alpha 16
  contraCmta : BitVec 32
  contraClearingAccount : Alpha 4
  contraOccAccount : BitVec 32
  contraCustAcct : Alpha 10
  contraOrderType : ContraOrderType
  contraPrice : BitVec 64
  contraQuantity : BitVec 32
  contraCapacity : ContraCapacity
  contraPositionEffectMask : BitVec 16
  contraStockLegShortSale : ContraStockLegShortSale
  contraStockLegMpid : Alpha 4
  contraStockCapacity : ContraStockCapacity
  flexLegPrices : Bounded 1 FlexLegPrices
  deriving DecidableEq, Repr

namespace NewCrossOrderMessage

def encode (message : NewCrossOrderMessage) : List UInt8 :=
  Alpha.encode message.firmId
    ++ (encodeUInt 4 message.instrumentId
    ++ (CrossType.encode message.crossType
    ++ (AuctionType.encode message.auctionType
    ++ (encodeUInt 1 message.auctionAllocPct
    ++ (Side.encode message.side
    ++ (Iso.encode message.iso
    ++ (PriceProtection.encode message.priceProtection
    ++ (encodeUInt 8 message.effectiveTime
    ++ (encodeUInt 1 message.disclosureMask
    ++ (encodeUInt 4 message.auctionDuration
    ++ (Alpha.encode message.reserved9
    ++ (Alpha.encode message.primaryClOrdId
    ++ (encodeUInt 4 message.primaryCmta
    ++ (Alpha.encode message.primaryClearingAccount
    ++ (encodeUInt 4 message.primaryOccAccount
    ++ (Alpha.encode message.primaryCustAcct
    ++ (encodeUInt 8 message.primaryPrice
    ++ (encodeUInt 4 message.primaryQuantity
    ++ (PrimaryCapacity.encode message.primaryCapacity
    ++ (encodeUInt 2 message.primaryPositionEffectMask
    ++ (PrimaryStockLegShortSale.encode message.primaryStockLegShortSale
    ++ (Alpha.encode message.primaryStockLegMpid
    ++ (PrimaryStockCapacity.encode message.primaryStockCapacity
    ++ (Alpha.encode message.contraClOrdId
    ++ (encodeUInt 4 message.contraCmta
    ++ (Alpha.encode message.contraClearingAccount
    ++ (encodeUInt 4 message.contraOccAccount
    ++ (Alpha.encode message.contraCustAcct
    ++ (ContraOrderType.encode message.contraOrderType
    ++ (encodeUInt 8 message.contraPrice
    ++ (encodeUInt 4 message.contraQuantity
    ++ (ContraCapacity.encode message.contraCapacity
    ++ (encodeUInt 2 message.contraPositionEffectMask
    ++ (ContraStockLegShortSale.encode message.contraStockLegShortSale
    ++ (Alpha.encode message.contraStockLegMpid
    ++ (ContraStockCapacity.encode message.contraStockCapacity
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.flexLegPrices.val.length)
    ++ (encodeMany FlexLegPrices.encode message.flexLegPrices.val))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewCrossOrderMessage × List UInt8) := do
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (auctionType, bytes) ← AuctionType.decode bytes
  let (auctionAllocPct, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← Side.decode bytes
  let (iso_, bytes) ← Iso.decode bytes
  let (priceProtection, bytes) ← PriceProtection.decode bytes
  let (effectiveTime, bytes) ← decodeUInt 8 bytes
  let (disclosureMask, bytes) ← decodeUInt 1 bytes
  let (auctionDuration, bytes) ← decodeUInt 4 bytes
  let (reserved9, bytes) ← Alpha.decode 9 bytes
  let (primaryClOrdId, bytes) ← Alpha.decode 16 bytes
  let (primaryCmta, bytes) ← decodeUInt 4 bytes
  let (primaryClearingAccount, bytes) ← Alpha.decode 4 bytes
  let (primaryOccAccount, bytes) ← decodeUInt 4 bytes
  let (primaryCustAcct, bytes) ← Alpha.decode 10 bytes
  let (primaryPrice, bytes) ← decodeUInt 8 bytes
  let (primaryQuantity, bytes) ← decodeUInt 4 bytes
  let (primaryCapacity, bytes) ← PrimaryCapacity.decode bytes
  let (primaryPositionEffectMask, bytes) ← decodeUInt 2 bytes
  let (primaryStockLegShortSale, bytes) ← PrimaryStockLegShortSale.decode bytes
  let (primaryStockLegMpid, bytes) ← Alpha.decode 4 bytes
  let (primaryStockCapacity, bytes) ← PrimaryStockCapacity.decode bytes
  let (contraClOrdId, bytes) ← Alpha.decode 16 bytes
  let (contraCmta, bytes) ← decodeUInt 4 bytes
  let (contraClearingAccount, bytes) ← Alpha.decode 4 bytes
  let (contraOccAccount, bytes) ← decodeUInt 4 bytes
  let (contraCustAcct, bytes) ← Alpha.decode 10 bytes
  let (contraOrderType, bytes) ← ContraOrderType.decode bytes
  let (contraPrice, bytes) ← decodeUInt 8 bytes
  let (contraQuantity, bytes) ← decodeUInt 4 bytes
  let (contraCapacity, bytes) ← ContraCapacity.decode bytes
  let (contraPositionEffectMask, bytes) ← decodeUInt 2 bytes
  let (contraStockLegShortSale, bytes) ← ContraStockLegShortSale.decode bytes
  let (contraStockLegMpid, bytes) ← Alpha.decode 4 bytes
  let (contraStockCapacity, bytes) ← ContraStockCapacity.decode bytes
  let (numberOfFlexLegs, bytes) ← decodeUInt 1 bytes
  let (flexLegPrices_, bytes) ← decodeMany FlexLegPrices.decode numberOfFlexLegs.toNat bytes
  if fits_flexLegPrices : flexLegPrices_.length < 256 ^ 1 then
    pure ({ firmId, instrumentId, crossType, auctionType, auctionAllocPct, side, iso := iso_, priceProtection, effectiveTime, disclosureMask, auctionDuration, reserved9, primaryClOrdId, primaryCmta, primaryClearingAccount, primaryOccAccount, primaryCustAcct, primaryPrice, primaryQuantity, primaryCapacity, primaryPositionEffectMask, primaryStockLegShortSale, primaryStockLegMpid, primaryStockCapacity, contraClOrdId, contraCmta, contraClearingAccount, contraOccAccount, contraCustAcct, contraOrderType, contraPrice, contraQuantity, contraCapacity, contraPositionEffectMask, contraStockLegShortSale, contraStockLegMpid, contraStockCapacity, flexLegPrices := ⟨flexLegPrices_, fits_flexLegPrices⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewCrossOrderMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewCrossOrderMessage) : (encode message).length ≤ 4236 := by
  have bound_flexLegPrices := message.flexLegPrices.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, CrossType.encode_length, AuctionType.encode_length, Side.encode_length, Iso.encode_length, PriceProtection.encode_length, PrimaryCapacity.encode_length, PrimaryStockLegShortSale.encode_length, PrimaryStockCapacity.encode_length, ContraOrderType.encode_length, ContraCapacity.encode_length, ContraStockLegShortSale.encode_length, ContraStockCapacity.encode_length, encodeMany_length_const FlexLegPrices.encode 16 FlexLegPrices.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewCrossOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AuctionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Iso.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PriceProtection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryStockLegShortSale.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PrimaryStockCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContraOrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContraCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ContraStockLegShortSale.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ContraStockCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 FlexLegPrices.encode FlexLegPrices.decode FlexLegPrices.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.flexLegPrices.length_lt]
  rfl

end NewCrossOrderMessage

/-- Trade Splits: 33 bytes -/
structure TradeSplits where
  allocQty : BitVec 32
  cmta : BitVec 32
  clearingAccount : Alpha 4
  occAccount : BitVec 32
  custAcct : Alpha 10
  stockLegMpid : Alpha 4
  capacity : Capacity
  openClose : OpenClose
  stockCapacity : StockCapacity
  deriving DecidableEq, Repr

namespace TradeSplits

def encode (message : TradeSplits) : List UInt8 :=
  encodeUInt 4 message.allocQty
    ++ (encodeUInt 4 message.cmta
    ++ (Alpha.encode message.clearingAccount
    ++ (encodeUInt 4 message.occAccount
    ++ (Alpha.encode message.custAcct
    ++ (Alpha.encode message.stockLegMpid
    ++ (Capacity.encode message.capacity
    ++ (OpenClose.encode message.openClose
    ++ (StockCapacity.encode message.stockCapacity))))))))

def decode (bytes : List UInt8) : Option (TradeSplits × List UInt8) := do
  let (allocQty, bytes) ← decodeUInt 4 bytes
  let (cmta, bytes) ← decodeUInt 4 bytes
  let (clearingAccount, bytes) ← Alpha.decode 4 bytes
  let (occAccount, bytes) ← decodeUInt 4 bytes
  let (custAcct, bytes) ← Alpha.decode 10 bytes
  let (stockLegMpid, bytes) ← Alpha.decode 4 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (openClose, bytes) ← OpenClose.decode bytes
  let (stockCapacity, bytes) ← StockCapacity.decode bytes
  pure ({ allocQty, cmta, clearingAccount, occAccount, custAcct, stockLegMpid, capacity, openClose, stockCapacity }, bytes)

@[simp] theorem encode_length (message : TradeSplits) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Capacity.encode_length, OpenClose.encode_length, StockCapacity.encode_length]

theorem encode_length_pos (message : TradeSplits) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeSplits) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OpenClose.decode_encode, some_bind]
  dsimp only
  rw [StockCapacity.decode_encode, some_bind]
  rfl

end TradeSplits

/-- Modify Trade Message -/
structure ModifyTradeMessage where
  firmId : Alpha 4
  instrumentId : BitVec 32
  clRequestId : Alpha 16
  clOrdId : Alpha 16
  crossId : BitVec 32
  matchId : BitVec 32
  side : Side
  quantity : BitVec 32
  tradeSplits : Bounded 2 TradeSplits
  deriving DecidableEq, Repr

namespace ModifyTradeMessage

def encode (message : ModifyTradeMessage) : List UInt8 :=
  Alpha.encode message.firmId
    ++ (encodeUInt 4 message.instrumentId
    ++ (Alpha.encode message.clRequestId
    ++ (Alpha.encode message.clOrdId
    ++ (encodeUInt 4 message.crossId
    ++ (encodeUInt 4 message.matchId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.tradeSplits.val.length)
    ++ (encodeMany TradeSplits.encode message.tradeSplits.val)))))))))

def decode (bytes : List UInt8) : Option (ModifyTradeMessage × List UInt8) := do
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (instrumentId, bytes) ← decodeUInt 4 bytes
  let (clRequestId, bytes) ← Alpha.decode 16 bytes
  let (clOrdId, bytes) ← Alpha.decode 16 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (numSplits, bytes) ← decodeUInt 2 bytes
  let (tradeSplits_, bytes) ← decodeMany TradeSplits.decode numSplits.toNat bytes
  if fits_tradeSplits : tradeSplits_.length < 256 ^ 2 then
    pure ({ firmId, instrumentId, clRequestId, clOrdId, crossId, matchId, side, quantity, tradeSplits := ⟨tradeSplits_, fits_tradeSplits⟩ }, bytes)
  else none

theorem encode_length_pos (message : ModifyTradeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ModifyTradeMessage) : (encode message).length ≤ 2162710 := by
  have bound_tradeSplits := message.tradeSplits.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, Side.encode_length, encodeMany_length_const TradeSplits.encode 33 TradeSplits.encode_length]
  omega

@[simp] theorem decode_encode (message : ModifyTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [decodeMany_bounded 2 TradeSplits.encode TradeSplits.decode TradeSplits.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.tradeSplits.length_lt]
  rfl

end ModifyTradeMessage

/-- Member Kill Switch Request Message: 25 bytes -/
structure MemberKillSwitchRequestMessage where
  firmId : Alpha 4
  clRequestId : Alpha 16
  targetFirmId : Alpha 4
  killAction : KillAction
  deriving DecidableEq, Repr

namespace MemberKillSwitchRequestMessage

def encode (message : MemberKillSwitchRequestMessage) : List UInt8 :=
  Alpha.encode message.firmId
    ++ (Alpha.encode message.clRequestId
    ++ (Alpha.encode message.targetFirmId
    ++ (KillAction.encode message.killAction)))

def decode (bytes : List UInt8) : Option (MemberKillSwitchRequestMessage × List UInt8) := do
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (clRequestId, bytes) ← Alpha.decode 16 bytes
  let (targetFirmId, bytes) ← Alpha.decode 4 bytes
  let (killAction, bytes) ← KillAction.decode bytes
  pure ({ firmId, clRequestId, targetFirmId, killAction }, bytes)

@[simp] theorem encode_length (message : MemberKillSwitchRequestMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, KillAction.encode_length]

theorem encode_length_pos (message : MemberKillSwitchRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MemberKillSwitchRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [KillAction.decode_encode, some_bind]
  rfl

end MemberKillSwitchRequestMessage

/-- Subscription Request Message: 36 bytes -/
structure SubscriptionRequestMessage where
  firmId : Alpha 4
  clRequestId : Alpha 16
  subscription : Alpha 16
  deriving DecidableEq, Repr

namespace SubscriptionRequestMessage

def encode (message : SubscriptionRequestMessage) : List UInt8 :=
  Alpha.encode message.firmId
    ++ (Alpha.encode message.clRequestId
    ++ (Alpha.encode message.subscription))

def decode (bytes : List UInt8) : Option (SubscriptionRequestMessage × List UInt8) := do
  let (firmId, bytes) ← Alpha.decode 4 bytes
  let (clRequestId, bytes) ← Alpha.decode 16 bytes
  let (subscription, bytes) ← Alpha.decode 16 bytes
  pure ({ firmId, clRequestId, subscription }, bytes)

@[simp] theorem encode_length (message : SubscriptionRequestMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SubscriptionRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SubscriptionRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SubscriptionRequestMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | newOrderLongFormMessage (message : NewOrderLongFormMessage) -- "A" 0x41
  | newOrderShortFormMessage (message : NewOrderShortFormMessage) -- "B" 0x42
  | replaceOrderMessage (message : ReplaceOrderMessage) -- "R" 0x52
  | cancelOrderMessage (message : CancelOrderMessage) -- "C" 0x43
  | massCancelMessage (message : MassCancelMessage) -- "U" 0x55
  | newCrossOrderMessage (message : NewCrossOrderMessage) -- "X" 0x58
  | modifyTradeMessage (message : ModifyTradeMessage) -- "M" 0x4D
  | memberKillSwitchRequestMessage (message : MemberKillSwitchRequestMessage) -- "K" 0x4B
  | subscriptionRequestMessage (message : SubscriptionRequestMessage) -- "F" 0x46
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .newOrderLongFormMessage _ => 65
  | .newOrderShortFormMessage _ => 66
  | .replaceOrderMessage _ => 82
  | .cancelOrderMessage _ => 67
  | .massCancelMessage _ => 85
  | .newCrossOrderMessage _ => 88
  | .modifyTradeMessage _ => 77
  | .memberKillSwitchRequestMessage _ => 75
  | .subscriptionRequestMessage _ => 70

def encode : UnsequencedMessage → List UInt8
  | .newOrderLongFormMessage message => NewOrderLongFormMessage.encode message
  | .newOrderShortFormMessage message => NewOrderShortFormMessage.encode message
  | .replaceOrderMessage message => ReplaceOrderMessage.encode message
  | .cancelOrderMessage message => CancelOrderMessage.encode message
  | .massCancelMessage message => MassCancelMessage.encode message
  | .newCrossOrderMessage message => NewCrossOrderMessage.encode message
  | .modifyTradeMessage message => ModifyTradeMessage.encode message
  | .memberKillSwitchRequestMessage message => MemberKillSwitchRequestMessage.encode message
  | .subscriptionRequestMessage message => SubscriptionRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 2162710 := by
  cases message with
  | newOrderLongFormMessage inner =>
    have bound_inner := NewOrderLongFormMessage.encode_length_le inner
    simp only [encode]
    omega
  | newOrderShortFormMessage inner =>
    simp only [encode, NewOrderShortFormMessage.encode_length]
    omega
  | replaceOrderMessage inner =>
    simp only [encode, ReplaceOrderMessage.encode_length]
    omega
  | cancelOrderMessage inner =>
    simp only [encode, CancelOrderMessage.encode_length]
    omega
  | massCancelMessage inner =>
    simp only [encode, MassCancelMessage.encode_length]
    omega
  | newCrossOrderMessage inner =>
    have bound_inner := NewCrossOrderMessage.encode_length_le inner
    simp only [encode]
    omega
  | modifyTradeMessage inner =>
    have bound_inner := ModifyTradeMessage.encode_length_le inner
    simp only [encode]
    omega
  | memberKillSwitchRequestMessage inner =>
    simp only [encode, MemberKillSwitchRequestMessage.encode_length]
    omega
  | subscriptionRequestMessage inner =>
    simp only [encode, SubscriptionRequestMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 65 then (NewOrderLongFormMessage.decode bytes).map fun (message, rest) => (.newOrderLongFormMessage message, rest)
  else if tag = 66 then (NewOrderShortFormMessage.decode bytes).map fun (message, rest) => (.newOrderShortFormMessage message, rest)
  else if tag = 82 then (ReplaceOrderMessage.decode bytes).map fun (message, rest) => (.replaceOrderMessage message, rest)
  else if tag = 67 then (CancelOrderMessage.decode bytes).map fun (message, rest) => (.cancelOrderMessage message, rest)
  else if tag = 85 then (MassCancelMessage.decode bytes).map fun (message, rest) => (.massCancelMessage message, rest)
  else if tag = 88 then (NewCrossOrderMessage.decode bytes).map fun (message, rest) => (.newCrossOrderMessage message, rest)
  else if tag = 77 then (ModifyTradeMessage.decode bytes).map fun (message, rest) => (.modifyTradeMessage message, rest)
  else if tag = 75 then (MemberKillSwitchRequestMessage.decode bytes).map fun (message, rest) => (.memberKillSwitchRequestMessage message, rest)
  else if tag = 70 then (SubscriptionRequestMessage.decode bytes).map fun (message, rest) => (.subscriptionRequestMessage message, rest)
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

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 2162711 := by
  unfold encode
  cases message.unsequencedMessage with
  | newOrderLongFormMessage inner =>
    have bound_inner := NewOrderLongFormMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | newOrderShortFormMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, NewOrderShortFormMessage.encode_length]
    omega
  | replaceOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ReplaceOrderMessage.encode_length]
    omega
  | cancelOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderMessage.encode_length]
    omega
  | massCancelMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MassCancelMessage.encode_length]
    omega
  | newCrossOrderMessage inner =>
    have bound_inner := NewCrossOrderMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | modifyTradeMessage inner =>
    have bound_inner := ModifyTradeMessage.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | memberKillSwitchRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MemberKillSwitchRequestMessage.encode_length]
    omega
  | subscriptionRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, SubscriptionRequestMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

end UnsequencedDataPacket

/-- Client Heartbeat Packet: 0 bytes -/
structure ClientHeartbeatPacket where
  deriving DecidableEq, Repr

namespace ClientHeartbeatPacket

def encode (_ : ClientHeartbeatPacket) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeatPacket × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeatPacket) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeatPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ClientHeartbeatPacket

/-- Logout Request Packet: 0 bytes -/
structure LogoutRequestPacket where
  deriving DecidableEq, Repr

namespace LogoutRequestPacket

def encode (_ : LogoutRequestPacket) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequestPacket × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequestPacket) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutRequestPacket

/-- Any Client Payload, selected by Client Packet Type -/
inductive ClientPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- "L" 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | clientHeartbeatPacket (message : ClientHeartbeatPacket) -- "R" 0x52
  | logoutRequestPacket (message : LogoutRequestPacket) -- "O" 0x4F
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .unsequencedDataPacket _ => 85
  | .clientHeartbeatPacket _ => 82
  | .logoutRequestPacket _ => 79

def encode : ClientPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .clientHeartbeatPacket message => ClientHeartbeatPacket.encode message
  | .logoutRequestPacket message => LogoutRequestPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 2162711 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [encode, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | clientHeartbeatPacket inner =>
    simp only [encode, ClientHeartbeatPacket.encode_length]
    omega
  | logoutRequestPacket inner =>
    simp only [encode, LogoutRequestPacket.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 76 then (LoginRequestPacket.decode bytes).map fun (message, rest) => (.loginRequestPacket message, rest)
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).map fun (message, rest) => (.unsequencedDataPacket message, rest)
  else if tag = 82 then (ClientHeartbeatPacket.decode bytes).map fun (message, rest) => (.clientHeartbeatPacket message, rest)
  else if tag = 79 then (LogoutRequestPacket.decode bytes).map fun (message, rest) => (.logoutRequestPacket message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Soup Bin Tcp Packet -/
structure ClientSoupBinTcpPacket where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSoupBinTcpPacket

def encodeBody (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option (ClientSoupBinTcpPacket × List UInt8) := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let (clientPayload, bytes) ← ClientPayload.decode clientPacketType bytes
  pure ({ clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (ClientSoupBinTcpPacket × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ClientSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
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

end Omi.NasdaqGemxoptionsOttoOuchV300Client
