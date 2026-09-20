import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Nordic Ouch 5 Order Entry v5.01.14

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Party Role Qualifier is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Liquidity Attributes is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Note: Server Soup Bin Tcp Packet's Packet Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNordicequitiesOrderentryOuchV50114Server

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x53, 0x45]

inductive EventCode where
  | startOfDay -- Start Of Day
  | endOfDay -- End Of Day
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfDay => 0x53
  | .endOfDay => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x53 then .startOfDay
  else .endOfDay

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfDay => decide
  | endOfDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Buy Sell Indicator: one byte code -/
def BuySellIndicator.codes : List UInt8 :=
  [0x42, 0x53]

inductive BuySellIndicator where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySellIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySellIndicator :=
  if byte = 0x42 then .buyOrder
  else .sellOrder

def ofByte (byte : UInt8) : BuySellIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySellIndicator) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuySellIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuySellIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuySellIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BuySellIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuySellIndicator

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x36, 0x37, 0x38, 0x39]

inductive Capacity where
  | client -- Client
  | ownAccount -- Own Account
  | marketMaker -- Market Maker
  | issuerHolding -- Issuer Holding
  | issuePriceStabilizing -- Issue Price Stabilizing
  | risklessPrincipal -- Riskless Principal
  | issuerHoldingDeal -- Issuer Holding Deal
  | issuePriceStabilizingDeal -- Issue Price Stabilizing Deal
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .client => 0x31
  | .ownAccount => 0x32
  | .marketMaker => 0x33
  | .issuerHolding => 0x34
  | .issuePriceStabilizing => 0x36
  | .risklessPrincipal => 0x37
  | .issuerHoldingDeal => 0x38
  | .issuePriceStabilizingDeal => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x31 then .client
  else if byte = 0x32 then .ownAccount
  else if byte = 0x33 then .marketMaker
  else if byte = 0x34 then .issuerHolding
  else if byte = 0x36 then .issuePriceStabilizing
  else if byte = 0x37 then .risklessPrincipal
  else if byte = 0x38 then .issuerHoldingDeal
  else .issuePriceStabilizingDeal

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | client => decide
  | ownAccount => decide
  | marketMaker => decide
  | issuerHolding => decide
  | issuePriceStabilizing => decide
  | risklessPrincipal => decide
  | issuerHoldingDeal => decide
  | issuePriceStabilizingDeal => decide
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

/-- Algo Indicator: one byte code -/
def AlgoIndicator.codes : List UInt8 :=
  [0x2D, 0x48]

inductive AlgoIndicator where
  | noAlgo -- No Algo
  | algo -- Algo
  | unlisted (byte : { byte : UInt8 // byte ∉ AlgoIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AlgoIndicator

def toByte : AlgoIndicator → UInt8
  | .noAlgo => 0x2D
  | .algo => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AlgoIndicator :=
  if byte = 0x2D then .noAlgo
  else .algo

def ofByte (byte : UInt8) : AlgoIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AlgoIndicator) : ofByte value.toByte = value := by
  cases value with
  | noAlgo => decide
  | algo => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AlgoIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AlgoIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AlgoIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AlgoIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AlgoIndicator

/-- Clearing Account Type Value: one byte code -/
def ClearingAccountTypeValue.codes : List UInt8 :=
  [0x31, 0x32]

inductive ClearingAccountTypeValue where
  | customerClient -- Customer Client
  | firmHouse -- Firm House
  | unlisted (byte : { byte : UInt8 // byte ∉ ClearingAccountTypeValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ClearingAccountTypeValue

def toByte : ClearingAccountTypeValue → UInt8
  | .customerClient => 0x31
  | .firmHouse => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ClearingAccountTypeValue :=
  if byte = 0x31 then .customerClient
  else .firmHouse

def ofByte (byte : UInt8) : ClearingAccountTypeValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ClearingAccountTypeValue) : ofByte value.toByte = value := by
  cases value with
  | customerClient => decide
  | firmHouse => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ClearingAccountTypeValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ClearingAccountTypeValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ClearingAccountTypeValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ClearingAccountTypeValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ClearingAccountTypeValue

/-- Cross Type Value: one byte code -/
def CrossTypeValue.codes : List UInt8 :=
  [0x43, 0x4F, 0x49, 0x48, 0x41]

inductive CrossTypeValue where
  | closingCross -- Closing Cross
  | openingCross -- Opening Cross
  | scheduledIntradayCross -- Scheduled Intraday Cross
  | haltCross -- Halt Cross
  | auctionOnDemand -- Auction On Demand
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossTypeValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossTypeValue

def toByte : CrossTypeValue → UInt8
  | .closingCross => 0x43
  | .openingCross => 0x4F
  | .scheduledIntradayCross => 0x49
  | .haltCross => 0x48
  | .auctionOnDemand => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossTypeValue :=
  if byte = 0x43 then .closingCross
  else if byte = 0x4F then .openingCross
  else if byte = 0x49 then .scheduledIntradayCross
  else if byte = 0x48 then .haltCross
  else .auctionOnDemand

def ofByte (byte : UInt8) : CrossTypeValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossTypeValue) : ofByte value.toByte = value := by
  cases value with
  | closingCross => decide
  | openingCross => decide
  | scheduledIntradayCross => decide
  | haltCross => decide
  | auctionOnDemand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossTypeValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossTypeValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossTypeValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CrossTypeValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossTypeValue

/-- Dea Indicator Value: one byte code -/
def DeaIndicatorValue.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x35]

inductive DeaIndicatorValue where
  | orderReceivedFromACustomer -- Order Received From A Customer
  | orderReceivedFromWithinTheFirm -- Order Received From Within The Firm
  | orderReceivedFromAnotherBrokerDealer -- Order Received From Another Broker Dealer
  | orderReceivedFromACustomerOrOriginatedWithTheFirm -- Order Received From A Customer Or Originated With The Firm
  | orderReceivedFromADirectAccessOrSponsoredAccessCustomer -- Order Received From A Direct Access Or Sponsored Access Customer
  | unlisted (byte : { byte : UInt8 // byte ∉ DeaIndicatorValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DeaIndicatorValue

def toByte : DeaIndicatorValue → UInt8
  | .orderReceivedFromACustomer => 0x31
  | .orderReceivedFromWithinTheFirm => 0x32
  | .orderReceivedFromAnotherBrokerDealer => 0x33
  | .orderReceivedFromACustomerOrOriginatedWithTheFirm => 0x34
  | .orderReceivedFromADirectAccessOrSponsoredAccessCustomer => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DeaIndicatorValue :=
  if byte = 0x31 then .orderReceivedFromACustomer
  else if byte = 0x32 then .orderReceivedFromWithinTheFirm
  else if byte = 0x33 then .orderReceivedFromAnotherBrokerDealer
  else if byte = 0x34 then .orderReceivedFromACustomerOrOriginatedWithTheFirm
  else .orderReceivedFromADirectAccessOrSponsoredAccessCustomer

def ofByte (byte : UInt8) : DeaIndicatorValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DeaIndicatorValue) : ofByte value.toByte = value := by
  cases value with
  | orderReceivedFromACustomer => decide
  | orderReceivedFromWithinTheFirm => decide
  | orderReceivedFromAnotherBrokerDealer => decide
  | orderReceivedFromACustomerOrOriginatedWithTheFirm => decide
  | orderReceivedFromADirectAccessOrSponsoredAccessCustomer => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DeaIndicatorValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DeaIndicatorValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DeaIndicatorValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DeaIndicatorValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DeaIndicatorValue

/-- Display Value: one byte code -/
def DisplayValue.codes : List UInt8 :=
  [0x59, 0x4E, 0x41, 0x4D]

inductive DisplayValue where
  | display -- Display
  | nonDisplay -- Non Display
  | auctionOnDemand -- Auction On Demand
  | nordicMid -- Nordic Mid
  | unlisted (byte : { byte : UInt8 // byte ∉ DisplayValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DisplayValue

def toByte : DisplayValue → UInt8
  | .display => 0x59
  | .nonDisplay => 0x4E
  | .auctionOnDemand => 0x41
  | .nordicMid => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DisplayValue :=
  if byte = 0x59 then .display
  else if byte = 0x4E then .nonDisplay
  else if byte = 0x41 then .auctionOnDemand
  else .nordicMid

def ofByte (byte : UInt8) : DisplayValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DisplayValue) : ofByte value.toByte = value := by
  cases value with
  | display => decide
  | nonDisplay => decide
  | auctionOnDemand => decide
  | nordicMid => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DisplayValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DisplayValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DisplayValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DisplayValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DisplayValue

/-- Liquidity Provision Indicator Value: one byte code -/
def LiquidityProvisionIndicatorValue.codes : List UInt8 :=
  [0x4E, 0x59]

inductive LiquidityProvisionIndicatorValue where
  | noLiquidityProvision -- No Liquidity Provision
  | liquidityProvision -- Liquidity Provision
  | unlisted (byte : { byte : UInt8 // byte ∉ LiquidityProvisionIndicatorValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LiquidityProvisionIndicatorValue

def toByte : LiquidityProvisionIndicatorValue → UInt8
  | .noLiquidityProvision => 0x4E
  | .liquidityProvision => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LiquidityProvisionIndicatorValue :=
  if byte = 0x4E then .noLiquidityProvision
  else .liquidityProvision

def ofByte (byte : UInt8) : LiquidityProvisionIndicatorValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LiquidityProvisionIndicatorValue) : ofByte value.toByte = value := by
  cases value with
  | noLiquidityProvision => decide
  | liquidityProvision => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LiquidityProvisionIndicatorValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LiquidityProvisionIndicatorValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LiquidityProvisionIndicatorValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LiquidityProvisionIndicatorValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LiquidityProvisionIndicatorValue

/-- Peg Type Value: one byte code -/
def PegTypeValue.codes : List UInt8 :=
  [0x4D, 0x50, 0x52]

inductive PegTypeValue where
  | midpoint -- Midpoint
  | market -- Market
  | primary -- Primary
  | unlisted (byte : { byte : UInt8 // byte ∉ PegTypeValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PegTypeValue

def toByte : PegTypeValue → UInt8
  | .midpoint => 0x4D
  | .market => 0x50
  | .primary => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PegTypeValue :=
  if byte = 0x4D then .midpoint
  else if byte = 0x50 then .market
  else .primary

def ofByte (byte : UInt8) : PegTypeValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PegTypeValue) : ofByte value.toByte = value := by
  cases value with
  | midpoint => decide
  | market => decide
  | primary => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PegTypeValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PegTypeValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PegTypeValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PegTypeValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PegTypeValue

/-- Stp Action Value: one byte code -/
def StpActionValue.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34]

inductive StpActionValue where
  | cancelPassiveOrder -- Cancel Passive Order
  | cancelAggressiveOrder -- Cancel Aggressive Order
  | cancelBothOrders -- Cancel Both Orders
  | createATransferTransaction -- Create A Transfer Transaction
  | unlisted (byte : { byte : UInt8 // byte ∉ StpActionValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StpActionValue

def toByte : StpActionValue → UInt8
  | .cancelPassiveOrder => 0x31
  | .cancelAggressiveOrder => 0x32
  | .cancelBothOrders => 0x33
  | .createATransferTransaction => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StpActionValue :=
  if byte = 0x31 then .cancelPassiveOrder
  else if byte = 0x32 then .cancelAggressiveOrder
  else if byte = 0x33 then .cancelBothOrders
  else .createATransferTransaction

def ofByte (byte : UInt8) : StpActionValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StpActionValue) : ofByte value.toByte = value := by
  cases value with
  | cancelPassiveOrder => decide
  | cancelAggressiveOrder => decide
  | cancelBothOrders => decide
  | createATransferTransaction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StpActionValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StpActionValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StpActionValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StpActionValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StpActionValue

/-- Stp Level Value: one byte code -/
def StpLevelValue.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive StpLevelValue where
  | mpidAndTrader -- Mpid And Trader
  | mpid -- Mpid
  | specifiedTraderGroup -- Specified Trader Group
  | unlisted (byte : { byte : UInt8 // byte ∉ StpLevelValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StpLevelValue

def toByte : StpLevelValue → UInt8
  | .mpidAndTrader => 0x31
  | .mpid => 0x32
  | .specifiedTraderGroup => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StpLevelValue :=
  if byte = 0x31 then .mpidAndTrader
  else if byte = 0x32 then .mpid
  else .specifiedTraderGroup

def ofByte (byte : UInt8) : StpLevelValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StpLevelValue) : ofByte value.toByte = value := by
  cases value with
  | mpidAndTrader => decide
  | mpid => decide
  | specifiedTraderGroup => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StpLevelValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StpLevelValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StpLevelValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StpLevelValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StpLevelValue

/-- Time In Force Value: one byte code -/
def TimeInForceValue.codes : List UInt8 :=
  [0x30, 0x31, 0x33, 0x36, 0x42]

inductive TimeInForceValue where
  | day -- Day
  | gtcGoodTillCancelled -- Gtc Good Till Cancelled
  | iocImmediateOrCancel -- Ioc Immediate Or Cancel
  | gttGoodTillTime -- Gtt Good Till Time
  | gfaGoodForAuction -- Gfa Good For Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForceValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForceValue

def toByte : TimeInForceValue → UInt8
  | .day => 0x30
  | .gtcGoodTillCancelled => 0x31
  | .iocImmediateOrCancel => 0x33
  | .gttGoodTillTime => 0x36
  | .gfaGoodForAuction => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForceValue :=
  if byte = 0x30 then .day
  else if byte = 0x31 then .gtcGoodTillCancelled
  else if byte = 0x33 then .iocImmediateOrCancel
  else if byte = 0x36 then .gttGoodTillTime
  else .gfaGoodForAuction

def ofByte (byte : UInt8) : TimeInForceValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForceValue) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | gtcGoodTillCancelled => decide
  | iocImmediateOrCancel => decide
  | gttGoodTillTime => decide
  | gfaGoodForAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForceValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForceValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForceValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TimeInForceValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForceValue

/-- Trading At Closing Price Value: one byte code -/
def TradingAtClosingPriceValue.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TradingAtClosingPriceValue where
  | participateInTradingAtClosingPrice -- Participate In Trading At Closing Price
  | doNotParticipateInTradingAtClosingPrice -- Do Not Participate In Trading At Closing Price
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingAtClosingPriceValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingAtClosingPriceValue

def toByte : TradingAtClosingPriceValue → UInt8
  | .participateInTradingAtClosingPrice => 0x59
  | .doNotParticipateInTradingAtClosingPrice => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingAtClosingPriceValue :=
  if byte = 0x59 then .participateInTradingAtClosingPrice
  else .doNotParticipateInTradingAtClosingPrice

def ofByte (byte : UInt8) : TradingAtClosingPriceValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingAtClosingPriceValue) : ofByte value.toByte = value := by
  cases value with
  | participateInTradingAtClosingPrice => decide
  | doNotParticipateInTradingAtClosingPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingAtClosingPriceValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingAtClosingPriceValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingAtClosingPriceValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingAtClosingPriceValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingAtClosingPriceValue

/-- Order Condition Value: one byte code -/
def OrderConditionValue.codes : List UInt8 :=
  [0x57, 0x55, 0x50, 0x51, 0x54]

inductive OrderConditionValue where
  | marketMakerOrder -- Market Maker Order
  | marketMakerOrderRefresh -- Market Maker Order Refresh
  | topofBook -- Topof Book
  | darklitSweep -- Darklit Sweep
  | tradeNow -- Trade Now
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderConditionValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderConditionValue

def toByte : OrderConditionValue → UInt8
  | .marketMakerOrder => 0x57
  | .marketMakerOrderRefresh => 0x55
  | .topofBook => 0x50
  | .darklitSweep => 0x51
  | .tradeNow => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderConditionValue :=
  if byte = 0x57 then .marketMakerOrder
  else if byte = 0x55 then .marketMakerOrderRefresh
  else if byte = 0x50 then .topofBook
  else if byte = 0x51 then .darklitSweep
  else .tradeNow

def ofByte (byte : UInt8) : OrderConditionValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderConditionValue) : ofByte value.toByte = value := by
  cases value with
  | marketMakerOrder => decide
  | marketMakerOrderRefresh => decide
  | topofBook => decide
  | darklitSweep => decide
  | tradeNow => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderConditionValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderConditionValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderConditionValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderConditionValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderConditionValue

/-- Customer Order Capacity Value: one byte code -/
def CustomerOrderCapacityValue.codes : List UInt8 :=
  [0x35]

inductive CustomerOrderCapacityValue where
  | retailCustomer -- Retail Customer
  | unlisted (byte : { byte : UInt8 // byte ∉ CustomerOrderCapacityValue.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustomerOrderCapacityValue

def toByte : CustomerOrderCapacityValue → UInt8
  | .retailCustomer => 0x35
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : CustomerOrderCapacityValue :=
  .retailCustomer

def ofByte (byte : UInt8) : CustomerOrderCapacityValue :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustomerOrderCapacityValue) : ofByte value.toByte = value := by
  cases value with
  | retailCustomer => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CustomerOrderCapacityValue) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CustomerOrderCapacityValue × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CustomerOrderCapacityValue) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CustomerOrderCapacityValue) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CustomerOrderCapacityValue

/-- Cancel Reason: one byte code -/
def CancelReason.codes : List UInt8 :=
  [0x55, 0x49, 0x54, 0x53, 0x51, 0x4C, 0x4E, 0x52]

inductive CancelReason where
  | userRequestedCancel -- User Requested Cancel
  | immediateOrCancelOrder -- Immediate Or Cancel Order
  | timeout -- Timeout
  | supervisory -- Supervisory
  | selfMatchPrevention -- Self Match Prevention
  | hiddenPegNotLis -- Hidden Peg Not Lis
  | badQuote -- Bad Quote
  | stateManagement -- State Management
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelReason

def toByte : CancelReason → UInt8
  | .userRequestedCancel => 0x55
  | .immediateOrCancelOrder => 0x49
  | .timeout => 0x54
  | .supervisory => 0x53
  | .selfMatchPrevention => 0x51
  | .hiddenPegNotLis => 0x4C
  | .badQuote => 0x4E
  | .stateManagement => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CancelReason :=
  if byte = 0x55 then .userRequestedCancel
  else if byte = 0x49 then .immediateOrCancelOrder
  else if byte = 0x54 then .timeout
  else if byte = 0x53 then .supervisory
  else if byte = 0x51 then .selfMatchPrevention
  else if byte = 0x4C then .hiddenPegNotLis
  else if byte = 0x4E then .badQuote
  else .stateManagement

def ofByte (byte : UInt8) : CancelReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelReason) : ofByte value.toByte = value := by
  cases value with
  | userRequestedCancel => decide
  | immediateOrCancelOrder => decide
  | timeout => decide
  | supervisory => decide
  | selfMatchPrevention => decide
  | hiddenPegNotLis => decide
  | badQuote => decide
  | stateManagement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CancelReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelReason

/-- Cancel Pending Reason: one byte code -/
def CancelPendingReason.codes : List UInt8 :=
  [0x41]

inductive CancelPendingReason where
  | cancelPendingCompletionOfAuctionOnDemand -- Cancel Pending Completion Of Auction On Demand
  | unlisted (byte : { byte : UInt8 // byte ∉ CancelPendingReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CancelPendingReason

def toByte : CancelPendingReason → UInt8
  | .cancelPendingCompletionOfAuctionOnDemand => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : CancelPendingReason :=
  .cancelPendingCompletionOfAuctionOnDemand

def ofByte (byte : UInt8) : CancelPendingReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CancelPendingReason) : ofByte value.toByte = value := by
  cases value with
  | cancelPendingCompletionOfAuctionOnDemand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CancelPendingReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CancelPendingReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CancelPendingReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CancelPendingReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CancelPendingReason

/-- Trading Mode: one byte code -/
def TradingMode.codes : List UInt8 :=
  [0x4F, 0x49, 0x55, 0x32, 0x33, 0x50]

inductive TradingMode where
  | openingAuction -- Opening Auction
  | scheduledIntradayAuction -- Scheduled Intraday Auction
  | unscheduledAuction -- Unscheduled Auction
  | continuousTrading -- Continuous Trading
  | atMarketCloseTrading -- At Market Close Trading
  | onDemandAuction -- On Demand Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingMode

def toByte : TradingMode → UInt8
  | .openingAuction => 0x4F
  | .scheduledIntradayAuction => 0x49
  | .unscheduledAuction => 0x55
  | .continuousTrading => 0x32
  | .atMarketCloseTrading => 0x33
  | .onDemandAuction => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingMode :=
  if byte = 0x4F then .openingAuction
  else if byte = 0x49 then .scheduledIntradayAuction
  else if byte = 0x55 then .unscheduledAuction
  else if byte = 0x32 then .continuousTrading
  else if byte = 0x33 then .atMarketCloseTrading
  else .onDemandAuction

def ofByte (byte : UInt8) : TradingMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingMode) : ofByte value.toByte = value := by
  cases value with
  | openingAuction => decide
  | scheduledIntradayAuction => decide
  | unscheduledAuction => decide
  | continuousTrading => decide
  | atMarketCloseTrading => decide
  | onDemandAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingMode

/-- Transaction Category: one byte code -/
def TransactionCategory.codes : List UInt8 :=
  [0x44, 0x2D]

inductive TransactionCategory where
  | darkTrade -- Dark Trade
  | noneApply -- None Apply
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionCategory

def toByte : TransactionCategory → UInt8
  | .darkTrade => 0x44
  | .noneApply => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionCategory :=
  if byte = 0x44 then .darkTrade
  else .noneApply

def ofByte (byte : UInt8) : TransactionCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionCategory) : ofByte value.toByte = value := by
  cases value with
  | darkTrade => decide
  | noneApply => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TransactionCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionCategory

/-- Transaction Type Algo Indicator: one byte code -/
def TransactionTypeAlgoIndicator.codes : List UInt8 :=
  [0x48, 0x2D]

inductive TransactionTypeAlgoIndicator where
  | algorithmicTrade -- Algorithmic Trade
  | noAlgorithmicTrade -- No Algorithmic Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ TransactionTypeAlgoIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TransactionTypeAlgoIndicator

def toByte : TransactionTypeAlgoIndicator → UInt8
  | .algorithmicTrade => 0x48
  | .noAlgorithmicTrade => 0x2D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TransactionTypeAlgoIndicator :=
  if byte = 0x48 then .algorithmicTrade
  else .noAlgorithmicTrade

def ofByte (byte : UInt8) : TransactionTypeAlgoIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TransactionTypeAlgoIndicator) : ofByte value.toByte = value := by
  cases value with
  | algorithmicTrade => decide
  | noAlgorithmicTrade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TransactionTypeAlgoIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TransactionTypeAlgoIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TransactionTypeAlgoIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TransactionTypeAlgoIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TransactionTypeAlgoIndicator

/-- Broken Trade Reason: one byte code -/
def BrokenTradeReason.codes : List UInt8 :=
  [0x45, 0x43, 0x53]

inductive BrokenTradeReason where
  | erroneous -- Erroneous
  | consent -- Consent
  | supervisory -- Supervisory
  | unlisted (byte : { byte : UInt8 // byte ∉ BrokenTradeReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BrokenTradeReason

def toByte : BrokenTradeReason → UInt8
  | .erroneous => 0x45
  | .consent => 0x43
  | .supervisory => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BrokenTradeReason :=
  if byte = 0x45 then .erroneous
  else if byte = 0x43 then .consent
  else .supervisory

def ofByte (byte : UInt8) : BrokenTradeReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BrokenTradeReason) : ofByte value.toByte = value := by
  cases value with
  | erroneous => decide
  | consent => decide
  | supervisory => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BrokenTradeReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BrokenTradeReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BrokenTradeReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BrokenTradeReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BrokenTradeReason

/-- Restate Reason: one byte code -/
def RestateReason.codes : List UInt8 :=
  [0x52, 0x50]

inductive RestateReason where
  | refreshOfDisplay -- Refresh Of Display
  | updateOfDisplayedPrice -- Update Of Displayed Price
  | unlisted (byte : { byte : UInt8 // byte ∉ RestateReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RestateReason

def toByte : RestateReason → UInt8
  | .refreshOfDisplay => 0x52
  | .updateOfDisplayedPrice => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RestateReason :=
  if byte = 0x52 then .refreshOfDisplay
  else .updateOfDisplayedPrice

def ofByte (byte : UInt8) : RestateReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RestateReason) : ofByte value.toByte = value := by
  cases value with
  | refreshOfDisplay => decide
  | updateOfDisplayedPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RestateReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RestateReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RestateReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RestateReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RestateReason

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

end DebugPacket

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  session : Alpha 10
  sequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.session
    ++ (Alpha.encode message.sequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ session, sequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  Alpha.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← Alpha.decode 1 bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRejectedPacket

/-- System Event Message: 9 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 64
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (EventCode.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ timestamp, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Clearing Account: 12 bytes -/
structure ClearingAccount where
  clearingAccountValue : Alpha 12
  deriving DecidableEq, Repr

namespace ClearingAccount

def encode (message : ClearingAccount) : List UInt8 :=
  Alpha.encode message.clearingAccountValue

def decode (bytes : List UInt8) : Option (ClearingAccount × List UInt8) := do
  let (clearingAccountValue, bytes) ← Alpha.decode 12 bytes
  pure ({ clearingAccountValue }, bytes)

@[simp] theorem encode_length (message : ClearingAccount) : (encode message).length = 12 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ClearingAccount) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingAccount) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClearingAccount

/-- Clearing Account Type: 1 bytes -/
structure ClearingAccountType where
  clearingAccountTypeValue : ClearingAccountTypeValue
  deriving DecidableEq, Repr

namespace ClearingAccountType

def encode (message : ClearingAccountType) : List UInt8 :=
  ClearingAccountTypeValue.encode message.clearingAccountTypeValue

def decode (bytes : List UInt8) : Option (ClearingAccountType × List UInt8) := do
  let (clearingAccountTypeValue, bytes) ← ClearingAccountTypeValue.decode bytes
  pure ({ clearingAccountTypeValue }, bytes)

@[simp] theorem encode_length (message : ClearingAccountType) : (encode message).length = 1 := by
  unfold encode
  simp only [ClearingAccountTypeValue.encode_length]

theorem encode_length_pos (message : ClearingAccountType) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingAccountType) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ClearingAccountTypeValue.decode_encode, some_bind]
  rfl

end ClearingAccountType

/-- Clearing Firm: 4 bytes -/
structure ClearingFirm where
  clearingFirmValue : Alpha 4
  deriving DecidableEq, Repr

namespace ClearingFirm

def encode (message : ClearingFirm) : List UInt8 :=
  Alpha.encode message.clearingFirmValue

def decode (bytes : List UInt8) : Option (ClearingFirm × List UInt8) := do
  let (clearingFirmValue, bytes) ← Alpha.decode 4 bytes
  pure ({ clearingFirmValue }, bytes)

@[simp] theorem encode_length (message : ClearingFirm) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ClearingFirm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingFirm) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClearingFirm

/-- Client Reference: 15 bytes -/
structure ClientReference where
  clientReferenceValue : Alpha 15
  deriving DecidableEq, Repr

namespace ClientReference

def encode (message : ClientReference) : List UInt8 :=
  Alpha.encode message.clientReferenceValue

def decode (bytes : List UInt8) : Option (ClientReference × List UInt8) := do
  let (clientReferenceValue, bytes) ← Alpha.decode 15 bytes
  pure ({ clientReferenceValue }, bytes)

@[simp] theorem encode_length (message : ClientReference) : (encode message).length = 15 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ClientReference) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClientReference) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClientReference

/-- Cross Type: 1 bytes -/
structure CrossType where
  crossTypeValue : CrossTypeValue
  deriving DecidableEq, Repr

namespace CrossType

def encode (message : CrossType) : List UInt8 :=
  CrossTypeValue.encode message.crossTypeValue

def decode (bytes : List UInt8) : Option (CrossType × List UInt8) := do
  let (crossTypeValue, bytes) ← CrossTypeValue.decode bytes
  pure ({ crossTypeValue }, bytes)

@[simp] theorem encode_length (message : CrossType) : (encode message).length = 1 := by
  unfold encode
  simp only [CrossTypeValue.encode_length]

theorem encode_length_pos (message : CrossType) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossType) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [CrossTypeValue.decode_encode, some_bind]
  rfl

end CrossType

/-- Dea Indicator: 1 bytes -/
structure DeaIndicator where
  deaIndicatorValue : DeaIndicatorValue
  deriving DecidableEq, Repr

namespace DeaIndicator

def encode (message : DeaIndicator) : List UInt8 :=
  DeaIndicatorValue.encode message.deaIndicatorValue

def decode (bytes : List UInt8) : Option (DeaIndicator × List UInt8) := do
  let (deaIndicatorValue, bytes) ← DeaIndicatorValue.decode bytes
  pure ({ deaIndicatorValue }, bytes)

@[simp] theorem encode_length (message : DeaIndicator) : (encode message).length = 1 := by
  unfold encode
  simp only [DeaIndicatorValue.encode_length]

theorem encode_length_pos (message : DeaIndicator) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeaIndicator) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [DeaIndicatorValue.decode_encode, some_bind]
  rfl

end DeaIndicator

/-- Display: 1 bytes -/
structure Display where
  displayValue : DisplayValue
  deriving DecidableEq, Repr

namespace Display

def encode (message : Display) : List UInt8 :=
  DisplayValue.encode message.displayValue

def decode (bytes : List UInt8) : Option (Display × List UInt8) := do
  let (displayValue, bytes) ← DisplayValue.decode bytes
  pure ({ displayValue }, bytes)

@[simp] theorem encode_length (message : Display) : (encode message).length = 1 := by
  unfold encode
  simp only [DisplayValue.encode_length]

theorem encode_length_pos (message : Display) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Display) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [DisplayValue.decode_encode, some_bind]
  rfl

end Display

/-- Display Price: 4 bytes -/
structure DisplayPrice where
  displayPriceValue : BitVec 32
  deriving DecidableEq, Repr

namespace DisplayPrice

def encode (message : DisplayPrice) : List UInt8 :=
  encodeUInt 4 message.displayPriceValue

def decode (bytes : List UInt8) : Option (DisplayPrice × List UInt8) := do
  let (displayPriceValue, bytes) ← decodeUInt 4 bytes
  pure ({ displayPriceValue }, bytes)

@[simp] theorem encode_length (message : DisplayPrice) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : DisplayPrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisplayPrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DisplayPrice

/-- Display Quantity: 4 bytes -/
structure DisplayQuantity where
  displayQuantityValue : BitVec 32
  deriving DecidableEq, Repr

namespace DisplayQuantity

def encode (message : DisplayQuantity) : List UInt8 :=
  encodeUInt 4 message.displayQuantityValue

def decode (bytes : List UInt8) : Option (DisplayQuantity × List UInt8) := do
  let (displayQuantityValue, bytes) ← decodeUInt 4 bytes
  pure ({ displayQuantityValue }, bytes)

@[simp] theorem encode_length (message : DisplayQuantity) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : DisplayQuantity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisplayQuantity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end DisplayQuantity

/-- Expire Time: 2 bytes -/
structure ExpireTime where
  expireTimeValue : BitVec 16
  deriving DecidableEq, Repr

namespace ExpireTime

def encode (message : ExpireTime) : List UInt8 :=
  encodeUInt 2 message.expireTimeValue

def decode (bytes : List UInt8) : Option (ExpireTime × List UInt8) := do
  let (expireTimeValue, bytes) ← decodeUInt 2 bytes
  pure ({ expireTimeValue }, bytes)

@[simp] theorem encode_length (message : ExpireTime) : (encode message).length = 2 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ExpireTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExpireTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExpireTime

/-- Firm: 4 bytes -/
structure Firm where
  firmValue : Alpha 4
  deriving DecidableEq, Repr

namespace Firm

def encode (message : Firm) : List UInt8 :=
  Alpha.encode message.firmValue

def decode (bytes : List UInt8) : Option (Firm × List UInt8) := do
  let (firmValue, bytes) ← Alpha.decode 4 bytes
  pure ({ firmValue }, bytes)

@[simp] theorem encode_length (message : Firm) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : Firm) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Firm) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end Firm

/-- Liquidity Provision Indicator: 1 bytes -/
structure LiquidityProvisionIndicator where
  liquidityProvisionIndicatorValue : LiquidityProvisionIndicatorValue
  deriving DecidableEq, Repr

namespace LiquidityProvisionIndicator

def encode (message : LiquidityProvisionIndicator) : List UInt8 :=
  LiquidityProvisionIndicatorValue.encode message.liquidityProvisionIndicatorValue

def decode (bytes : List UInt8) : Option (LiquidityProvisionIndicator × List UInt8) := do
  let (liquidityProvisionIndicatorValue, bytes) ← LiquidityProvisionIndicatorValue.decode bytes
  pure ({ liquidityProvisionIndicatorValue }, bytes)

@[simp] theorem encode_length (message : LiquidityProvisionIndicator) : (encode message).length = 1 := by
  unfold encode
  simp only [LiquidityProvisionIndicatorValue.encode_length]

theorem encode_length_pos (message : LiquidityProvisionIndicator) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LiquidityProvisionIndicator) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [LiquidityProvisionIndicatorValue.decode_encode, some_bind]
  rfl

end LiquidityProvisionIndicator

/-- Max Floor: 4 bytes -/
structure MaxFloor where
  maxFloorValue : BitVec 32
  deriving DecidableEq, Repr

namespace MaxFloor

def encode (message : MaxFloor) : List UInt8 :=
  encodeUInt 4 message.maxFloorValue

def decode (bytes : List UInt8) : Option (MaxFloor × List UInt8) := do
  let (maxFloorValue, bytes) ← decodeUInt 4 bytes
  pure ({ maxFloorValue }, bytes)

@[simp] theorem encode_length (message : MaxFloor) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MaxFloor) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaxFloor) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MaxFloor

/-- Minimum Quantity: 4 bytes -/
structure MinimumQuantity where
  minimumQuantityValue : BitVec 32
  deriving DecidableEq, Repr

namespace MinimumQuantity

def encode (message : MinimumQuantity) : List UInt8 :=
  encodeUInt 4 message.minimumQuantityValue

def decode (bytes : List UInt8) : Option (MinimumQuantity × List UInt8) := do
  let (minimumQuantityValue, bytes) ← decodeUInt 4 bytes
  pure ({ minimumQuantityValue }, bytes)

@[simp] theorem encode_length (message : MinimumQuantity) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MinimumQuantity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MinimumQuantity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MinimumQuantity

/-- Order Reference: 10 bytes -/
structure OrderReference where
  orderReferenceValue : Alpha 10
  deriving DecidableEq, Repr

namespace OrderReference

def encode (message : OrderReference) : List UInt8 :=
  Alpha.encode message.orderReferenceValue

def decode (bytes : List UInt8) : Option (OrderReference × List UInt8) := do
  let (orderReferenceValue, bytes) ← Alpha.decode 10 bytes
  pure ({ orderReferenceValue }, bytes)

@[simp] theorem encode_length (message : OrderReference) : (encode message).length = 10 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : OrderReference) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReference) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderReference

/-- Original Order Entry Date: 4 bytes -/
structure OriginalOrderEntryDate where
  originalOrderEntryDateValue : BitVec 32
  deriving DecidableEq, Repr

namespace OriginalOrderEntryDate

def encode (message : OriginalOrderEntryDate) : List UInt8 :=
  encodeUInt 4 message.originalOrderEntryDateValue

def decode (bytes : List UInt8) : Option (OriginalOrderEntryDate × List UInt8) := do
  let (originalOrderEntryDateValue, bytes) ← decodeUInt 4 bytes
  pure ({ originalOrderEntryDateValue }, bytes)

@[simp] theorem encode_length (message : OriginalOrderEntryDate) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : OriginalOrderEntryDate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OriginalOrderEntryDate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OriginalOrderEntryDate

/-- Original Order Reference Number: 8 bytes -/
structure OriginalOrderReferenceNumber where
  originalOrderReferenceNumberValue : BitVec 64
  deriving DecidableEq, Repr

namespace OriginalOrderReferenceNumber

def encode (message : OriginalOrderReferenceNumber) : List UInt8 :=
  encodeUInt 8 message.originalOrderReferenceNumberValue

def decode (bytes : List UInt8) : Option (OriginalOrderReferenceNumber × List UInt8) := do
  let (originalOrderReferenceNumberValue, bytes) ← decodeUInt 8 bytes
  pure ({ originalOrderReferenceNumberValue }, bytes)

@[simp] theorem encode_length (message : OriginalOrderReferenceNumber) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : OriginalOrderReferenceNumber) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OriginalOrderReferenceNumber) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OriginalOrderReferenceNumber

/-- Peg Difference: 4 bytes -/
structure PegDifference where
  pegDifferenceValue : BitVec 32
  deriving DecidableEq, Repr

namespace PegDifference

def encode (message : PegDifference) : List UInt8 :=
  encodeUInt 4 message.pegDifferenceValue

def decode (bytes : List UInt8) : Option (PegDifference × List UInt8) := do
  let (pegDifferenceValue, bytes) ← decodeUInt 4 bytes
  pure ({ pegDifferenceValue }, bytes)

@[simp] theorem encode_length (message : PegDifference) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : PegDifference) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PegDifference) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PegDifference

/-- Peg Type: 1 bytes -/
structure PegType where
  pegTypeValue : PegTypeValue
  deriving DecidableEq, Repr

namespace PegType

def encode (message : PegType) : List UInt8 :=
  PegTypeValue.encode message.pegTypeValue

def decode (bytes : List UInt8) : Option (PegType × List UInt8) := do
  let (pegTypeValue, bytes) ← PegTypeValue.decode bytes
  pure ({ pegTypeValue }, bytes)

@[simp] theorem encode_length (message : PegType) : (encode message).length = 1 := by
  unfold encode
  simp only [PegTypeValue.encode_length]

theorem encode_length_pos (message : PegType) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PegType) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [PegTypeValue.decode_encode, some_bind]
  rfl

end PegType

/-- Random Reserve: 4 bytes -/
structure RandomReserve where
  randomReserveValue : BitVec 32
  deriving DecidableEq, Repr

namespace RandomReserve

def encode (message : RandomReserve) : List UInt8 :=
  encodeUInt 4 message.randomReserveValue

def decode (bytes : List UInt8) : Option (RandomReserve × List UInt8) := do
  let (randomReserveValue, bytes) ← decodeUInt 4 bytes
  pure ({ randomReserveValue }, bytes)

@[simp] theorem encode_length (message : RandomReserve) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : RandomReserve) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RandomReserve) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RandomReserve

/-- Secondary Order Reference Number: 8 bytes -/
structure SecondaryOrderReferenceNumber where
  secondaryOrderReferenceNumberValue : BitVec 64
  deriving DecidableEq, Repr

namespace SecondaryOrderReferenceNumber

def encode (message : SecondaryOrderReferenceNumber) : List UInt8 :=
  encodeUInt 8 message.secondaryOrderReferenceNumberValue

def decode (bytes : List UInt8) : Option (SecondaryOrderReferenceNumber × List UInt8) := do
  let (secondaryOrderReferenceNumberValue, bytes) ← decodeUInt 8 bytes
  pure ({ secondaryOrderReferenceNumberValue }, bytes)

@[simp] theorem encode_length (message : SecondaryOrderReferenceNumber) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecondaryOrderReferenceNumber) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondaryOrderReferenceNumber) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecondaryOrderReferenceNumber

/-- Stp Action: 1 bytes -/
structure StpAction where
  stpActionValue : StpActionValue
  deriving DecidableEq, Repr

namespace StpAction

def encode (message : StpAction) : List UInt8 :=
  StpActionValue.encode message.stpActionValue

def decode (bytes : List UInt8) : Option (StpAction × List UInt8) := do
  let (stpActionValue, bytes) ← StpActionValue.decode bytes
  pure ({ stpActionValue }, bytes)

@[simp] theorem encode_length (message : StpAction) : (encode message).length = 1 := by
  unfold encode
  simp only [StpActionValue.encode_length]

theorem encode_length_pos (message : StpAction) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StpAction) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [StpActionValue.decode_encode, some_bind]
  rfl

end StpAction

/-- Stp Level: 1 bytes -/
structure StpLevel where
  stpLevelValue : StpLevelValue
  deriving DecidableEq, Repr

namespace StpLevel

def encode (message : StpLevel) : List UInt8 :=
  StpLevelValue.encode message.stpLevelValue

def decode (bytes : List UInt8) : Option (StpLevel × List UInt8) := do
  let (stpLevelValue, bytes) ← StpLevelValue.decode bytes
  pure ({ stpLevelValue }, bytes)

@[simp] theorem encode_length (message : StpLevel) : (encode message).length = 1 := by
  unfold encode
  simp only [StpLevelValue.encode_length]

theorem encode_length_pos (message : StpLevel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StpLevel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [StpLevelValue.decode_encode, some_bind]
  rfl

end StpLevel

/-- Stp Trader Group: 2 bytes -/
structure StpTraderGroup where
  stpTraderGroupValue : Alpha 2
  deriving DecidableEq, Repr

namespace StpTraderGroup

def encode (message : StpTraderGroup) : List UInt8 :=
  Alpha.encode message.stpTraderGroupValue

def decode (bytes : List UInt8) : Option (StpTraderGroup × List UInt8) := do
  let (stpTraderGroupValue, bytes) ← Alpha.decode 2 bytes
  pure ({ stpTraderGroupValue }, bytes)

@[simp] theorem encode_length (message : StpTraderGroup) : (encode message).length = 2 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : StpTraderGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StpTraderGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end StpTraderGroup

/-- Time In Force: 1 bytes -/
structure TimeInForce where
  timeInForceValue : TimeInForceValue
  deriving DecidableEq, Repr

namespace TimeInForce

def encode (message : TimeInForce) : List UInt8 :=
  TimeInForceValue.encode message.timeInForceValue

def decode (bytes : List UInt8) : Option (TimeInForce × List UInt8) := do
  let (timeInForceValue, bytes) ← TimeInForceValue.decode bytes
  pure ({ timeInForceValue }, bytes)

@[simp] theorem encode_length (message : TimeInForce) : (encode message).length = 1 := by
  unfold encode
  simp only [TimeInForceValue.encode_length]

theorem encode_length_pos (message : TimeInForce) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeInForce) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [TimeInForceValue.decode_encode, some_bind]
  rfl

end TimeInForce

/-- Trading At Closing Price: 1 bytes -/
structure TradingAtClosingPrice where
  tradingAtClosingPriceValue : TradingAtClosingPriceValue
  deriving DecidableEq, Repr

namespace TradingAtClosingPrice

def encode (message : TradingAtClosingPrice) : List UInt8 :=
  TradingAtClosingPriceValue.encode message.tradingAtClosingPriceValue

def decode (bytes : List UInt8) : Option (TradingAtClosingPrice × List UInt8) := do
  let (tradingAtClosingPriceValue, bytes) ← TradingAtClosingPriceValue.decode bytes
  pure ({ tradingAtClosingPriceValue }, bytes)

@[simp] theorem encode_length (message : TradingAtClosingPrice) : (encode message).length = 1 := by
  unfold encode
  simp only [TradingAtClosingPriceValue.encode_length]

theorem encode_length_pos (message : TradingAtClosingPrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingAtClosingPrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [TradingAtClosingPriceValue.decode_encode, some_bind]
  rfl

end TradingAtClosingPrice

/-- Order Condition: 1 bytes -/
structure OrderCondition where
  orderConditionValue : OrderConditionValue
  deriving DecidableEq, Repr

namespace OrderCondition

def encode (message : OrderCondition) : List UInt8 :=
  OrderConditionValue.encode message.orderConditionValue

def decode (bytes : List UInt8) : Option (OrderCondition × List UInt8) := do
  let (orderConditionValue, bytes) ← OrderConditionValue.decode bytes
  pure ({ orderConditionValue }, bytes)

@[simp] theorem encode_length (message : OrderCondition) : (encode message).length = 1 := by
  unfold encode
  simp only [OrderConditionValue.encode_length]

theorem encode_length_pos (message : OrderCondition) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCondition) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [OrderConditionValue.decode_encode, some_bind]
  rfl

end OrderCondition

/-- Cumulative Quantity: 4 bytes -/
structure CumulativeQuantity where
  cumulativeQuantityValue : BitVec 32
  deriving DecidableEq, Repr

namespace CumulativeQuantity

def encode (message : CumulativeQuantity) : List UInt8 :=
  encodeUInt 4 message.cumulativeQuantityValue

def decode (bytes : List UInt8) : Option (CumulativeQuantity × List UInt8) := do
  let (cumulativeQuantityValue, bytes) ← decodeUInt 4 bytes
  pure ({ cumulativeQuantityValue }, bytes)

@[simp] theorem encode_length (message : CumulativeQuantity) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : CumulativeQuantity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CumulativeQuantity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CumulativeQuantity

/-- Customer Order Capacity: 1 bytes -/
structure CustomerOrderCapacity where
  customerOrderCapacityValue : CustomerOrderCapacityValue
  deriving DecidableEq, Repr

namespace CustomerOrderCapacity

def encode (message : CustomerOrderCapacity) : List UInt8 :=
  CustomerOrderCapacityValue.encode message.customerOrderCapacityValue

def decode (bytes : List UInt8) : Option (CustomerOrderCapacity × List UInt8) := do
  let (customerOrderCapacityValue, bytes) ← CustomerOrderCapacityValue.decode bytes
  pure ({ customerOrderCapacityValue }, bytes)

@[simp] theorem encode_length (message : CustomerOrderCapacity) : (encode message).length = 1 := by
  unfold encode
  simp only [CustomerOrderCapacityValue.encode_length]

theorem encode_length_pos (message : CustomerOrderCapacity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CustomerOrderCapacity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [CustomerOrderCapacityValue.decode_encode, some_bind]
  rfl

end CustomerOrderCapacity

/-- Any Value Payload, selected by Tag -/
inductive ValuePayload where
  | clearingAccount (message : ClearingAccount) -- 1
  | clearingAccountType (message : ClearingAccountType) -- 2
  | clearingFirm (message : ClearingFirm) -- 3
  | clientReference (message : ClientReference) -- 4
  | crossType (message : CrossType) -- 5
  | deaIndicator (message : DeaIndicator) -- 6
  | display (message : Display) -- 7
  | displayPrice (message : DisplayPrice) -- 8
  | displayQuantity (message : DisplayQuantity) -- 9
  | expireTime (message : ExpireTime) -- 10
  | firm (message : Firm) -- 11
  | liquidityProvisionIndicator (message : LiquidityProvisionIndicator) -- 12
  | maxFloor (message : MaxFloor) -- 13
  | minimumQuantity (message : MinimumQuantity) -- 14
  | orderReference (message : OrderReference) -- 15
  | originalOrderEntryDate (message : OriginalOrderEntryDate) -- 16
  | originalOrderReferenceNumber (message : OriginalOrderReferenceNumber) -- 17
  | pegDifference (message : PegDifference) -- 18
  | pegType (message : PegType) -- 19
  | randomReserve (message : RandomReserve) -- 20
  | secondaryOrderReferenceNumber (message : SecondaryOrderReferenceNumber) -- 21
  | stpAction (message : StpAction) -- 22
  | stpLevel (message : StpLevel) -- 23
  | stpTraderGroup (message : StpTraderGroup) -- 24
  | timeInForce (message : TimeInForce) -- 25
  | tradingAtClosingPrice (message : TradingAtClosingPrice) -- 26
  | orderCondition (message : OrderCondition) -- 27
  | cumulativeQuantity (message : CumulativeQuantity) -- 28
  | customerOrderCapacity (message : CustomerOrderCapacity) -- 29
  deriving DecidableEq, Repr

namespace ValuePayload

/-- The Tag each message is sent under -/
def tag : ValuePayload → BitVec 8
  | .clearingAccount _ => 1
  | .clearingAccountType _ => 2
  | .clearingFirm _ => 3
  | .clientReference _ => 4
  | .crossType _ => 5
  | .deaIndicator _ => 6
  | .display _ => 7
  | .displayPrice _ => 8
  | .displayQuantity _ => 9
  | .expireTime _ => 10
  | .firm _ => 11
  | .liquidityProvisionIndicator _ => 12
  | .maxFloor _ => 13
  | .minimumQuantity _ => 14
  | .orderReference _ => 15
  | .originalOrderEntryDate _ => 16
  | .originalOrderReferenceNumber _ => 17
  | .pegDifference _ => 18
  | .pegType _ => 19
  | .randomReserve _ => 20
  | .secondaryOrderReferenceNumber _ => 21
  | .stpAction _ => 22
  | .stpLevel _ => 23
  | .stpTraderGroup _ => 24
  | .timeInForce _ => 25
  | .tradingAtClosingPrice _ => 26
  | .orderCondition _ => 27
  | .cumulativeQuantity _ => 28
  | .customerOrderCapacity _ => 29

def encode : ValuePayload → List UInt8
  | .clearingAccount message => ClearingAccount.encode message
  | .clearingAccountType message => ClearingAccountType.encode message
  | .clearingFirm message => ClearingFirm.encode message
  | .clientReference message => ClientReference.encode message
  | .crossType message => CrossType.encode message
  | .deaIndicator message => DeaIndicator.encode message
  | .display message => Display.encode message
  | .displayPrice message => DisplayPrice.encode message
  | .displayQuantity message => DisplayQuantity.encode message
  | .expireTime message => ExpireTime.encode message
  | .firm message => Firm.encode message
  | .liquidityProvisionIndicator message => LiquidityProvisionIndicator.encode message
  | .maxFloor message => MaxFloor.encode message
  | .minimumQuantity message => MinimumQuantity.encode message
  | .orderReference message => OrderReference.encode message
  | .originalOrderEntryDate message => OriginalOrderEntryDate.encode message
  | .originalOrderReferenceNumber message => OriginalOrderReferenceNumber.encode message
  | .pegDifference message => PegDifference.encode message
  | .pegType message => PegType.encode message
  | .randomReserve message => RandomReserve.encode message
  | .secondaryOrderReferenceNumber message => SecondaryOrderReferenceNumber.encode message
  | .stpAction message => StpAction.encode message
  | .stpLevel message => StpLevel.encode message
  | .stpTraderGroup message => StpTraderGroup.encode message
  | .timeInForce message => TimeInForce.encode message
  | .tradingAtClosingPrice message => TradingAtClosingPrice.encode message
  | .orderCondition message => OrderCondition.encode message
  | .cumulativeQuantity message => CumulativeQuantity.encode message
  | .customerOrderCapacity message => CustomerOrderCapacity.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ValuePayload) : (encode message).length ≤ 15 := by
  cases message with
  | clearingAccount inner =>
    simp only [encode, ClearingAccount.encode_length]
    omega
  | clearingAccountType inner =>
    simp only [encode, ClearingAccountType.encode_length]
    omega
  | clearingFirm inner =>
    simp only [encode, ClearingFirm.encode_length]
    omega
  | clientReference inner =>
    simp only [encode, ClientReference.encode_length]
    omega
  | crossType inner =>
    simp only [encode, CrossType.encode_length]
    omega
  | deaIndicator inner =>
    simp only [encode, DeaIndicator.encode_length]
    omega
  | display inner =>
    simp only [encode, Display.encode_length]
    omega
  | displayPrice inner =>
    simp only [encode, DisplayPrice.encode_length]
    omega
  | displayQuantity inner =>
    simp only [encode, DisplayQuantity.encode_length]
    omega
  | expireTime inner =>
    simp only [encode, ExpireTime.encode_length]
    omega
  | firm inner =>
    simp only [encode, Firm.encode_length]
    omega
  | liquidityProvisionIndicator inner =>
    simp only [encode, LiquidityProvisionIndicator.encode_length]
    omega
  | maxFloor inner =>
    simp only [encode, MaxFloor.encode_length]
    omega
  | minimumQuantity inner =>
    simp only [encode, MinimumQuantity.encode_length]
    omega
  | orderReference inner =>
    simp only [encode, OrderReference.encode_length]
    omega
  | originalOrderEntryDate inner =>
    simp only [encode, OriginalOrderEntryDate.encode_length]
    omega
  | originalOrderReferenceNumber inner =>
    simp only [encode, OriginalOrderReferenceNumber.encode_length]
    omega
  | pegDifference inner =>
    simp only [encode, PegDifference.encode_length]
    omega
  | pegType inner =>
    simp only [encode, PegType.encode_length]
    omega
  | randomReserve inner =>
    simp only [encode, RandomReserve.encode_length]
    omega
  | secondaryOrderReferenceNumber inner =>
    simp only [encode, SecondaryOrderReferenceNumber.encode_length]
    omega
  | stpAction inner =>
    simp only [encode, StpAction.encode_length]
    omega
  | stpLevel inner =>
    simp only [encode, StpLevel.encode_length]
    omega
  | stpTraderGroup inner =>
    simp only [encode, StpTraderGroup.encode_length]
    omega
  | timeInForce inner =>
    simp only [encode, TimeInForce.encode_length]
    omega
  | tradingAtClosingPrice inner =>
    simp only [encode, TradingAtClosingPrice.encode_length]
    omega
  | orderCondition inner =>
    simp only [encode, OrderCondition.encode_length]
    omega
  | cumulativeQuantity inner =>
    simp only [encode, CumulativeQuantity.encode_length]
    omega
  | customerOrderCapacity inner =>
    simp only [encode, CustomerOrderCapacity.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ValuePayload × List UInt8) :=
  if tag = 1 then (ClearingAccount.decode bytes).map fun (message, rest) => (.clearingAccount message, rest)
  else if tag = 2 then (ClearingAccountType.decode bytes).map fun (message, rest) => (.clearingAccountType message, rest)
  else if tag = 3 then (ClearingFirm.decode bytes).map fun (message, rest) => (.clearingFirm message, rest)
  else if tag = 4 then (ClientReference.decode bytes).map fun (message, rest) => (.clientReference message, rest)
  else if tag = 5 then (CrossType.decode bytes).map fun (message, rest) => (.crossType message, rest)
  else if tag = 6 then (DeaIndicator.decode bytes).map fun (message, rest) => (.deaIndicator message, rest)
  else if tag = 7 then (Display.decode bytes).map fun (message, rest) => (.display message, rest)
  else if tag = 8 then (DisplayPrice.decode bytes).map fun (message, rest) => (.displayPrice message, rest)
  else if tag = 9 then (DisplayQuantity.decode bytes).map fun (message, rest) => (.displayQuantity message, rest)
  else if tag = 10 then (ExpireTime.decode bytes).map fun (message, rest) => (.expireTime message, rest)
  else if tag = 11 then (Firm.decode bytes).map fun (message, rest) => (.firm message, rest)
  else if tag = 12 then (LiquidityProvisionIndicator.decode bytes).map fun (message, rest) => (.liquidityProvisionIndicator message, rest)
  else if tag = 13 then (MaxFloor.decode bytes).map fun (message, rest) => (.maxFloor message, rest)
  else if tag = 14 then (MinimumQuantity.decode bytes).map fun (message, rest) => (.minimumQuantity message, rest)
  else if tag = 15 then (OrderReference.decode bytes).map fun (message, rest) => (.orderReference message, rest)
  else if tag = 16 then (OriginalOrderEntryDate.decode bytes).map fun (message, rest) => (.originalOrderEntryDate message, rest)
  else if tag = 17 then (OriginalOrderReferenceNumber.decode bytes).map fun (message, rest) => (.originalOrderReferenceNumber message, rest)
  else if tag = 18 then (PegDifference.decode bytes).map fun (message, rest) => (.pegDifference message, rest)
  else if tag = 19 then (PegType.decode bytes).map fun (message, rest) => (.pegType message, rest)
  else if tag = 20 then (RandomReserve.decode bytes).map fun (message, rest) => (.randomReserve message, rest)
  else if tag = 21 then (SecondaryOrderReferenceNumber.decode bytes).map fun (message, rest) => (.secondaryOrderReferenceNumber message, rest)
  else if tag = 22 then (StpAction.decode bytes).map fun (message, rest) => (.stpAction message, rest)
  else if tag = 23 then (StpLevel.decode bytes).map fun (message, rest) => (.stpLevel message, rest)
  else if tag = 24 then (StpTraderGroup.decode bytes).map fun (message, rest) => (.stpTraderGroup message, rest)
  else if tag = 25 then (TimeInForce.decode bytes).map fun (message, rest) => (.timeInForce message, rest)
  else if tag = 26 then (TradingAtClosingPrice.decode bytes).map fun (message, rest) => (.tradingAtClosingPrice message, rest)
  else if tag = 27 then (OrderCondition.decode bytes).map fun (message, rest) => (.orderCondition message, rest)
  else if tag = 28 then (CumulativeQuantity.decode bytes).map fun (message, rest) => (.cumulativeQuantity message, rest)
  else if tag = 29 then (CustomerOrderCapacity.decode bytes).map fun (message, rest) => (.customerOrderCapacity message, rest)
  else none

@[simp] theorem decode_encode (message : ValuePayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ValuePayload

/-- TagValue -/
structure Tagvalue where
  valuePayload : ValuePayload
  deriving DecidableEq, Repr

namespace Tagvalue

def encodeBody (message : Tagvalue) : List UInt8 :=
  encodeUInt 1 (ValuePayload.tag message.valuePayload)
    ++ (ValuePayload.encode message.valuePayload)

def decodeBody (bytes : List UInt8) : Option (Tagvalue × List UInt8) := do
  let (tag, bytes) ← decodeUInt 1 bytes
  let (valuePayload, bytes) ← ValuePayload.decode tag bytes
  pure ({ valuePayload }, bytes)

theorem decodeBody_encodeBody (message : Tagvalue) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ValuePayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Tagvalue) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.valuePayload with
  | clearingAccount inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, ClearingAccount.encode_length]
    omega
  | clearingAccountType inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, ClearingAccountType.encode_length]
    omega
  | clearingFirm inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, ClearingFirm.encode_length]
    omega
  | clientReference inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, ClientReference.encode_length]
    omega
  | crossType inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, CrossType.encode_length]
    omega
  | deaIndicator inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, DeaIndicator.encode_length]
    omega
  | display inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, Display.encode_length]
    omega
  | displayPrice inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, DisplayPrice.encode_length]
    omega
  | displayQuantity inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, DisplayQuantity.encode_length]
    omega
  | expireTime inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, ExpireTime.encode_length]
    omega
  | firm inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, Firm.encode_length]
    omega
  | liquidityProvisionIndicator inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, LiquidityProvisionIndicator.encode_length]
    omega
  | maxFloor inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, MaxFloor.encode_length]
    omega
  | minimumQuantity inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, MinimumQuantity.encode_length]
    omega
  | orderReference inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, OrderReference.encode_length]
    omega
  | originalOrderEntryDate inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, OriginalOrderEntryDate.encode_length]
    omega
  | originalOrderReferenceNumber inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, OriginalOrderReferenceNumber.encode_length]
    omega
  | pegDifference inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, PegDifference.encode_length]
    omega
  | pegType inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, PegType.encode_length]
    omega
  | randomReserve inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, RandomReserve.encode_length]
    omega
  | secondaryOrderReferenceNumber inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, SecondaryOrderReferenceNumber.encode_length]
    omega
  | stpAction inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, StpAction.encode_length]
    omega
  | stpLevel inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, StpLevel.encode_length]
    omega
  | stpTraderGroup inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, StpTraderGroup.encode_length]
    omega
  | timeInForce inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, TimeInForce.encode_length]
    omega
  | tradingAtClosingPrice inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, TradingAtClosingPrice.encode_length]
    omega
  | orderCondition inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, OrderCondition.encode_length]
    omega
  | cumulativeQuantity inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, CumulativeQuantity.encode_length]
    omega
  | customerOrderCapacity inner =>
    simp only [ValuePayload.encode, List.length_append, encodeUInt_length, CustomerOrderCapacity.encode_length]
    omega

/-- Size rule: Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Tagvalue → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (Tagvalue × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : Tagvalue) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Tagvalue) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Tagvalue

/-- Order Accepted Message -/
structure OrderAcceptedMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  price : BitVec 32
  orderReferenceNumber : BitVec 64
  buySellIndicator : BuySellIndicator
  orderBook : BitVec 32
  quantity : BitVec 32
  user : Alpha 6
  executionWithinFirm : BitVec 32
  investmentDecisionWithinFirmShortCode : BitVec 32
  clientIdentifier : BitVec 32
  partyRoleQualifier : BitVec 8
  capacity : Capacity
  algoIndicator : AlgoIndicator
  tagvalue : Sized 2 Tagvalue.encode
  deriving DecidableEq, Repr

namespace OrderAcceptedMessage

def encode (message : OrderAcceptedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.orderBook
    ++ (encodeUInt 4 message.quantity
    ++ (Alpha.encode message.user
    ++ (encodeUInt 4 message.executionWithinFirm
    ++ (encodeUInt 4 message.investmentDecisionWithinFirmShortCode
    ++ (encodeUInt 4 message.clientIdentifier
    ++ (encodeUInt 1 message.partyRoleQualifier
    ++ (Capacity.encode message.capacity
    ++ (AlgoIndicator.encode message.algoIndicator
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany Tagvalue.encode message.tagvalue.val).length)
    ++ (encodeMany Tagvalue.encode message.tagvalue.val)))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAcceptedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (user, bytes) ← Alpha.decode 6 bytes
  let (executionWithinFirm, bytes) ← decodeUInt 4 bytes
  let (investmentDecisionWithinFirmShortCode, bytes) ← decodeUInt 4 bytes
  let (clientIdentifier, bytes) ← decodeUInt 4 bytes
  let (partyRoleQualifier, bytes) ← decodeUInt 1 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  let (algoIndicator, bytes) ← AlgoIndicator.decode bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (tagvalue_, bytes) ← decodeSized Tagvalue.decode appendageLength.toNat bytes
  if fits_tagvalue : (encodeMany Tagvalue.encode tagvalue_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, price, orderReferenceNumber, buySellIndicator, orderBook, quantity, user, executionWithinFirm, investmentDecisionWithinFirmShortCode, clientIdentifier, partyRoleQualifier, capacity, algoIndicator, tagvalue := ⟨tagvalue_, fits_tagvalue⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderAcceptedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderAcceptedMessage) : (encode message).length ≤ 65591 := by
  have bound_tagvalue := message.tagvalue.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, BuySellIndicator.encode_length, Alpha.encode_length, Capacity.encode_length, AlgoIndicator.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderAcceptedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Capacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AlgoIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 Tagvalue.encode Tagvalue.decode Tagvalue.decode_encode Tagvalue.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.tagvalue.length_lt]
  rfl

end OrderAcceptedMessage

/-- Order Replaced Message -/
structure OrderReplacedMessage where
  timestamp : BitVec 64
  origUserRefNum : BitVec 32
  newUserRefNum : BitVec 32
  price : BitVec 32
  orderReferenceNumber : BitVec 64
  buySellIndicator : BuySellIndicator
  orderBook : BitVec 32
  quantity : BitVec 32
  user : Alpha 6
  tagvalue : Sized 2 Tagvalue.encode
  deriving DecidableEq, Repr

namespace OrderReplacedMessage

def encode (message : OrderReplacedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.origUserRefNum
    ++ (encodeUInt 4 message.newUserRefNum
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.orderBook
    ++ (encodeUInt 4 message.quantity
    ++ (Alpha.encode message.user
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany Tagvalue.encode message.tagvalue.val).length)
    ++ (encodeMany Tagvalue.encode message.tagvalue.val))))))))))

def decode (bytes : List UInt8) : Option (OrderReplacedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (origUserRefNum, bytes) ← decodeUInt 4 bytes
  let (newUserRefNum, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (user, bytes) ← Alpha.decode 6 bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (tagvalue_, bytes) ← decodeSized Tagvalue.decode appendageLength.toNat bytes
  if fits_tagvalue : (encodeMany Tagvalue.encode tagvalue_).length < 256 ^ 2 then
    pure ({ timestamp, origUserRefNum, newUserRefNum, price, orderReferenceNumber, buySellIndicator, orderBook, quantity, user, tagvalue := ⟨tagvalue_, fits_tagvalue⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderReplacedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderReplacedMessage) : (encode message).length ≤ 65580 := by
  have bound_tagvalue := message.tagvalue.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, BuySellIndicator.encode_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderReplacedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 Tagvalue.encode Tagvalue.decode Tagvalue.decode_encode Tagvalue.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.tagvalue.length_lt]
  rfl

end OrderReplacedMessage

/-- Cancelled Order Message: 17 bytes -/
structure CancelledOrderMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  decrementQuantity : BitVec 32
  cancelReason : CancelReason
  deriving DecidableEq, Repr

namespace CancelledOrderMessage

def encode (message : CancelledOrderMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.decrementQuantity
    ++ (CancelReason.encode message.cancelReason)))

def decode (bytes : List UInt8) : Option (CancelledOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (decrementQuantity, bytes) ← decodeUInt 4 bytes
  let (cancelReason, bytes) ← CancelReason.decode bytes
  pure ({ timestamp, userRefNum, decrementQuantity, cancelReason }, bytes)

@[simp] theorem encode_length (message : CancelledOrderMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CancelReason.encode_length]

theorem encode_length_pos (message : CancelledOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelledOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CancelReason.decode_encode, some_bind]
  rfl

end CancelledOrderMessage

/-- Cancel Pending Message: 13 bytes -/
structure CancelPendingMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  cancelPendingReason : CancelPendingReason
  deriving DecidableEq, Repr

namespace CancelPendingMessage

def encode (message : CancelPendingMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (CancelPendingReason.encode message.cancelPendingReason))

def decode (bytes : List UInt8) : Option (CancelPendingMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (cancelPendingReason, bytes) ← CancelPendingReason.decode bytes
  pure ({ timestamp, userRefNum, cancelPendingReason }, bytes)

@[simp] theorem encode_length (message : CancelPendingMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CancelPendingReason.encode_length]

theorem encode_length_pos (message : CancelPendingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelPendingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [CancelPendingReason.decode_encode, some_bind]
  rfl

end CancelPendingMessage

/-- Replace Pending Message: 17 bytes -/
structure ReplacePendingMessage where
  timestamp : BitVec 64
  origUserRefNum : BitVec 32
  userRefNum : BitVec 32
  replacePendingReason : Alpha 1
  deriving DecidableEq, Repr

namespace ReplacePendingMessage

def encode (message : ReplacePendingMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.origUserRefNum
    ++ (encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.replacePendingReason)))

def decode (bytes : List UInt8) : Option (ReplacePendingMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (origUserRefNum, bytes) ← decodeUInt 4 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (replacePendingReason, bytes) ← Alpha.decode 1 bytes
  pure ({ timestamp, origUserRefNum, userRefNum, replacePendingReason }, bytes)

@[simp] theorem encode_length (message : ReplacePendingMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ReplacePendingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplacePendingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ReplacePendingMessage

/-- Executed Order Message: 34 bytes -/
structure ExecutedOrderMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  executedQuantity : BitVec 32
  executionPrice : BitVec 32
  liquidityFlag : Alpha 1
  matchNumber : BitVec 32
  contraFirm : Alpha 4
  tradingMode : TradingMode
  transactionCategory : TransactionCategory
  transactionTypeAlgoIndicator : TransactionTypeAlgoIndicator
  liquidityAttributes : BitVec 8
  lastMarket : BitVec 8
  deriving DecidableEq, Repr

namespace ExecutedOrderMessage

def encode (message : ExecutedOrderMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.executionPrice
    ++ (Alpha.encode message.liquidityFlag
    ++ (encodeUInt 4 message.matchNumber
    ++ (Alpha.encode message.contraFirm
    ++ (TradingMode.encode message.tradingMode
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (TransactionTypeAlgoIndicator.encode message.transactionTypeAlgoIndicator
    ++ (encodeUInt 1 message.liquidityAttributes
    ++ (encodeUInt 1 message.lastMarket)))))))))))

def decode (bytes : List UInt8) : Option (ExecutedOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 4 bytes
  let (liquidityFlag, bytes) ← Alpha.decode 1 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (contraFirm, bytes) ← Alpha.decode 4 bytes
  let (tradingMode, bytes) ← TradingMode.decode bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (transactionTypeAlgoIndicator, bytes) ← TransactionTypeAlgoIndicator.decode bytes
  let (liquidityAttributes, bytes) ← decodeUInt 1 bytes
  let (lastMarket, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, userRefNum, executedQuantity, executionPrice, liquidityFlag, matchNumber, contraFirm, tradingMode, transactionCategory, transactionTypeAlgoIndicator, liquidityAttributes, lastMarket }, bytes)

@[simp] theorem encode_length (message : ExecutedOrderMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TradingMode.encode_length, TransactionCategory.encode_length, TransactionTypeAlgoIndicator.encode_length]

theorem encode_length_pos (message : ExecutedOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutedOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingMode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionTypeAlgoIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutedOrderMessage

/-- Broken Trade Message: 20 bytes -/
structure BrokenTradeMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  matchNumber : BitVec 32
  brokenTradeReason : BrokenTradeReason
  tradingMode : TradingMode
  transactionCategory : TransactionCategory
  transactionTypeAlgoIndicator : TransactionTypeAlgoIndicator
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.matchNumber
    ++ (BrokenTradeReason.encode message.brokenTradeReason
    ++ (TradingMode.encode message.tradingMode
    ++ (TransactionCategory.encode message.transactionCategory
    ++ (TransactionTypeAlgoIndicator.encode message.transactionTypeAlgoIndicator))))))

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (brokenTradeReason, bytes) ← BrokenTradeReason.decode bytes
  let (tradingMode, bytes) ← TradingMode.decode bytes
  let (transactionCategory, bytes) ← TransactionCategory.decode bytes
  let (transactionTypeAlgoIndicator, bytes) ← TransactionTypeAlgoIndicator.decode bytes
  pure ({ timestamp, userRefNum, matchNumber, brokenTradeReason, tradingMode, transactionCategory, transactionTypeAlgoIndicator }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BrokenTradeReason.encode_length, TradingMode.encode_length, TransactionCategory.encode_length, TransactionTypeAlgoIndicator.encode_length]

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
  rw [List.append_assoc, BrokenTradeReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingMode.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactionCategory.decode_encode, some_bind]
  dsimp only
  rw [TransactionTypeAlgoIndicator.decode_encode, some_bind]
  rfl

end BrokenTradeMessage

/-- Rejected Order Message: 14 bytes -/
structure RejectedOrderMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  rejectedOrderReason : BitVec 16
  deriving DecidableEq, Repr

namespace RejectedOrderMessage

def encode (message : RejectedOrderMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 2 message.rejectedOrderReason))

def decode (bytes : List UInt8) : Option (RejectedOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (rejectedOrderReason, bytes) ← decodeUInt 2 bytes
  pure ({ timestamp, userRefNum, rejectedOrderReason }, bytes)

@[simp] theorem encode_length (message : RejectedOrderMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : RejectedOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectedOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RejectedOrderMessage

/-- Cancel Rejected Message: 14 bytes -/
structure CancelRejectedMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  cancelRejectedReason : BitVec 16
  deriving DecidableEq, Repr

namespace CancelRejectedMessage

def encode (message : CancelRejectedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 2 message.cancelRejectedReason))

def decode (bytes : List UInt8) : Option (CancelRejectedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (cancelRejectedReason, bytes) ← decodeUInt 2 bytes
  pure ({ timestamp, userRefNum, cancelRejectedReason }, bytes)

@[simp] theorem encode_length (message : CancelRejectedMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : CancelRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CancelRejectedMessage

/-- Order Restated Message -/
structure OrderRestatedMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  restateReason : RestateReason
  tagvalue : Sized 2 Tagvalue.encode
  deriving DecidableEq, Repr

namespace OrderRestatedMessage

def encode (message : OrderRestatedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (RestateReason.encode message.restateReason
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) (encodeMany Tagvalue.encode message.tagvalue.val).length)
    ++ (encodeMany Tagvalue.encode message.tagvalue.val))))

def decode (bytes : List UInt8) : Option (OrderRestatedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (restateReason, bytes) ← RestateReason.decode bytes
  let (appendageLength, bytes) ← decodeUInt 2 bytes
  let (tagvalue_, bytes) ← decodeSized Tagvalue.decode appendageLength.toNat bytes
  if fits_tagvalue : (encodeMany Tagvalue.encode tagvalue_).length < 256 ^ 2 then
    pure ({ timestamp, userRefNum, restateReason, tagvalue := ⟨tagvalue_, fits_tagvalue⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderRestatedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderRestatedMessage) : (encode message).length ≤ 65550 := by
  have bound_tagvalue := message.tagvalue.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, RestateReason.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderRestatedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RestateReason.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeSized_encodeMany 2 Tagvalue.encode Tagvalue.decode Tagvalue.decode_encode Tagvalue.encode_length_pos, some_bind]
  dsimp only
  rw [dite_eq_left message.tagvalue.length_lt]
  rfl

end OrderRestatedMessage

/-- Mmo Refresh Request Message: 17 bytes -/
structure MmoRefreshRequestMessage where
  timestamp : BitVec 64
  firm : Firm
  orderBook : BitVec 32
  mmoRefreshReason : Alpha 1
  deriving DecidableEq, Repr

namespace MmoRefreshRequestMessage

def encode (message : MmoRefreshRequestMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Firm.encode message.firm
    ++ (encodeUInt 4 message.orderBook
    ++ (Alpha.encode message.mmoRefreshReason)))

def decode (bytes : List UInt8) : Option (MmoRefreshRequestMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (firm, bytes) ← Firm.decode bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (mmoRefreshReason, bytes) ← Alpha.decode 1 bytes
  pure ({ timestamp, firm, orderBook, mmoRefreshReason }, bytes)

@[simp] theorem encode_length (message : MmoRefreshRequestMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Firm.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : MmoRefreshRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmoRefreshRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Firm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MmoRefreshRequestMessage

/-- Account Query Response Message: 12 bytes -/
structure AccountQueryResponseMessage where
  timestamp : BitVec 64
  nextUserRefNum : BitVec 32
  deriving DecidableEq, Repr

namespace AccountQueryResponseMessage

def encode (message : AccountQueryResponseMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.nextUserRefNum)

def decode (bytes : List UInt8) : Option (AccountQueryResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (nextUserRefNum, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, nextUserRefNum }, bytes)

@[simp] theorem encode_length (message : AccountQueryResponseMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : AccountQueryResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AccountQueryResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AccountQueryResponseMessage

/-- Gtc Cancelled Message: 22 bytes -/
structure GtcCancelledMessage where
  timestamp : BitVec 64
  originalOrderEntryDate : OriginalOrderEntryDate
  originalOrderReferenceNumber : OriginalOrderReferenceNumber
  reason : BitVec 16
  deriving DecidableEq, Repr

namespace GtcCancelledMessage

def encode (message : GtcCancelledMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (OriginalOrderEntryDate.encode message.originalOrderEntryDate
    ++ (OriginalOrderReferenceNumber.encode message.originalOrderReferenceNumber
    ++ (encodeUInt 2 message.reason)))

def decode (bytes : List UInt8) : Option (GtcCancelledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (originalOrderEntryDate, bytes) ← OriginalOrderEntryDate.decode bytes
  let (originalOrderReferenceNumber, bytes) ← OriginalOrderReferenceNumber.decode bytes
  let (reason, bytes) ← decodeUInt 2 bytes
  pure ({ timestamp, originalOrderEntryDate, originalOrderReferenceNumber, reason }, bytes)

@[simp] theorem encode_length (message : GtcCancelledMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OriginalOrderEntryDate.encode_length, OriginalOrderReferenceNumber.encode_length]

theorem encode_length_pos (message : GtcCancelledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GtcCancelledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalOrderEntryDate.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OriginalOrderReferenceNumber.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end GtcCancelledMessage

/-- Response To Mmi Notification Message: 29 bytes -/
structure ResponseToMmiNotificationMessage where
  timestamp : BitVec 64
  userRefNum : BitVec 32
  orderBook : BitVec 32
  instruction : Alpha 1
  addOrRemove : Alpha 1
  firm : Firm
  user : Alpha 6
  instructionStatus : Alpha 1
  deriving DecidableEq, Repr

namespace ResponseToMmiNotificationMessage

def encode (message : ResponseToMmiNotificationMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.userRefNum
    ++ (encodeUInt 4 message.orderBook
    ++ (Alpha.encode message.instruction
    ++ (Alpha.encode message.addOrRemove
    ++ (Firm.encode message.firm
    ++ (Alpha.encode message.user
    ++ (Alpha.encode message.instructionStatus)))))))

def decode (bytes : List UInt8) : Option (ResponseToMmiNotificationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (instruction, bytes) ← Alpha.decode 1 bytes
  let (addOrRemove, bytes) ← Alpha.decode 1 bytes
  let (firm, bytes) ← Firm.decode bytes
  let (user, bytes) ← Alpha.decode 6 bytes
  let (instructionStatus, bytes) ← Alpha.decode 1 bytes
  pure ({ timestamp, userRefNum, orderBook, instruction, addOrRemove, firm, user, instructionStatus }, bytes)

@[simp] theorem encode_length (message : ResponseToMmiNotificationMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Firm.encode_length]

theorem encode_length_pos (message : ResponseToMmiNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResponseToMmiNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Firm.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ResponseToMmiNotificationMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- 'S' 0x53
  | orderAcceptedMessage (message : OrderAcceptedMessage) -- 'A' 0x41
  | orderReplacedMessage (message : OrderReplacedMessage) -- 'U' 0x55
  | cancelledOrderMessage (message : CancelledOrderMessage) -- 'C' 0x43
  | cancelPendingMessage (message : CancelPendingMessage) -- 'P' 0x50
  | replacePendingMessage (message : ReplacePendingMessage) -- 'N' 0x4E
  | executedOrderMessage (message : ExecutedOrderMessage) -- 'E' 0x45
  | brokenTradeMessage (message : BrokenTradeMessage) -- 'B' 0x42
  | rejectedOrderMessage (message : RejectedOrderMessage) -- 'J' 0x4A
  | cancelRejectedMessage (message : CancelRejectedMessage) -- 'I' 0x49
  | orderRestatedMessage (message : OrderRestatedMessage) -- 'T' 0x54
  | mmoRefreshRequestMessage (message : MmoRefreshRequestMessage) -- 'W' 0x57
  | accountQueryResponseMessage (message : AccountQueryResponseMessage) -- 'Q' 0x51
  | gtcCancelledMessage (message : GtcCancelledMessage) -- 'G' 0x47
  | responseToMmiNotificationMessage (message : ResponseToMmiNotificationMessage) -- 'R' 0x52
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .orderAcceptedMessage _ => 65
  | .orderReplacedMessage _ => 85
  | .cancelledOrderMessage _ => 67
  | .cancelPendingMessage _ => 80
  | .replacePendingMessage _ => 78
  | .executedOrderMessage _ => 69
  | .brokenTradeMessage _ => 66
  | .rejectedOrderMessage _ => 74
  | .cancelRejectedMessage _ => 73
  | .orderRestatedMessage _ => 84
  | .mmoRefreshRequestMessage _ => 87
  | .accountQueryResponseMessage _ => 81
  | .gtcCancelledMessage _ => 71
  | .responseToMmiNotificationMessage _ => 82

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .orderAcceptedMessage message => OrderAcceptedMessage.encode message
  | .orderReplacedMessage message => OrderReplacedMessage.encode message
  | .cancelledOrderMessage message => CancelledOrderMessage.encode message
  | .cancelPendingMessage message => CancelPendingMessage.encode message
  | .replacePendingMessage message => ReplacePendingMessage.encode message
  | .executedOrderMessage message => ExecutedOrderMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .rejectedOrderMessage message => RejectedOrderMessage.encode message
  | .cancelRejectedMessage message => CancelRejectedMessage.encode message
  | .orderRestatedMessage message => OrderRestatedMessage.encode message
  | .mmoRefreshRequestMessage message => MmoRefreshRequestMessage.encode message
  | .accountQueryResponseMessage message => AccountQueryResponseMessage.encode message
  | .gtcCancelledMessage message => GtcCancelledMessage.encode message
  | .responseToMmiNotificationMessage message => ResponseToMmiNotificationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 65591 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | orderAcceptedMessage inner =>
    have bound_inner := OrderAcceptedMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderReplacedMessage inner =>
    have bound_inner := OrderReplacedMessage.encode_length_le inner
    simp only [encode]
    omega
  | cancelledOrderMessage inner =>
    simp only [encode, CancelledOrderMessage.encode_length]
    omega
  | cancelPendingMessage inner =>
    simp only [encode, CancelPendingMessage.encode_length]
    omega
  | replacePendingMessage inner =>
    simp only [encode, ReplacePendingMessage.encode_length]
    omega
  | executedOrderMessage inner =>
    simp only [encode, ExecutedOrderMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | rejectedOrderMessage inner =>
    simp only [encode, RejectedOrderMessage.encode_length]
    omega
  | cancelRejectedMessage inner =>
    simp only [encode, CancelRejectedMessage.encode_length]
    omega
  | orderRestatedMessage inner =>
    have bound_inner := OrderRestatedMessage.encode_length_le inner
    simp only [encode]
    omega
  | mmoRefreshRequestMessage inner =>
    simp only [encode, MmoRefreshRequestMessage.encode_length]
    omega
  | accountQueryResponseMessage inner =>
    simp only [encode, AccountQueryResponseMessage.encode_length]
    omega
  | gtcCancelledMessage inner =>
    simp only [encode, GtcCancelledMessage.encode_length]
    omega
  | responseToMmiNotificationMessage inner =>
    simp only [encode, ResponseToMmiNotificationMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 65 then (OrderAcceptedMessage.decode bytes).map fun (message, rest) => (.orderAcceptedMessage message, rest)
  else if tag = 85 then (OrderReplacedMessage.decode bytes).map fun (message, rest) => (.orderReplacedMessage message, rest)
  else if tag = 67 then (CancelledOrderMessage.decode bytes).map fun (message, rest) => (.cancelledOrderMessage message, rest)
  else if tag = 80 then (CancelPendingMessage.decode bytes).map fun (message, rest) => (.cancelPendingMessage message, rest)
  else if tag = 78 then (ReplacePendingMessage.decode bytes).map fun (message, rest) => (.replacePendingMessage message, rest)
  else if tag = 69 then (ExecutedOrderMessage.decode bytes).map fun (message, rest) => (.executedOrderMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 74 then (RejectedOrderMessage.decode bytes).map fun (message, rest) => (.rejectedOrderMessage message, rest)
  else if tag = 73 then (CancelRejectedMessage.decode bytes).map fun (message, rest) => (.cancelRejectedMessage message, rest)
  else if tag = 84 then (OrderRestatedMessage.decode bytes).map fun (message, rest) => (.orderRestatedMessage message, rest)
  else if tag = 87 then (MmoRefreshRequestMessage.decode bytes).map fun (message, rest) => (.mmoRefreshRequestMessage message, rest)
  else if tag = 81 then (AccountQueryResponseMessage.decode bytes).map fun (message, rest) => (.accountQueryResponseMessage message, rest)
  else if tag = 71 then (GtcCancelledMessage.decode bytes).map fun (message, rest) => (.gtcCancelledMessage message, rest)
  else if tag = 82 then (ResponseToMmiNotificationMessage.decode bytes).map fun (message, rest) => (.responseToMmiNotificationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 65592 := by
  unfold encode
  cases message.sequencedMessage with
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | orderAcceptedMessage inner =>
    have bound_inner := OrderAcceptedMessage.encode_length_le inner
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | orderReplacedMessage inner =>
    have bound_inner := OrderReplacedMessage.encode_length_le inner
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | cancelledOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, CancelledOrderMessage.encode_length]
    omega
  | cancelPendingMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, CancelPendingMessage.encode_length]
    omega
  | replacePendingMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ReplacePendingMessage.encode_length]
    omega
  | executedOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ExecutedOrderMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | rejectedOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, RejectedOrderMessage.encode_length]
    omega
  | cancelRejectedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, CancelRejectedMessage.encode_length]
    omega
  | orderRestatedMessage inner =>
    have bound_inner := OrderRestatedMessage.encode_length_le inner
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | mmoRefreshRequestMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, MmoRefreshRequestMessage.encode_length]
    omega
  | accountQueryResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AccountQueryResponseMessage.encode_length]
    omega
  | gtcCancelledMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, GtcCancelledMessage.encode_length]
    omega
  | responseToMmiNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ResponseToMmiNotificationMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

end SequencedDataPacket

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

end ServerHeartbeat

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

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- '+' 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- 'A' 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- 'J' 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- 'S' 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- 'H' 0x48
  | endOfSession (message : EndOfSession) -- 'Z' 0x5A
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83
  | .serverHeartbeat _ => 72
  | .endOfSession _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .endOfSession message => EndOfSession.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 65592 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [encode, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [encode, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).map fun (message, rest) => (.loginAcceptedPacket message, rest)
  else if tag = 74 then (LoginRejectedPacket.decode bytes).map fun (message, rest) => (.loginRejectedPacket message, rest)
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun (message, rest) => (.sequencedDataPacket message, rest)
  else if tag = 72 then (ServerHeartbeat.decode bytes).map fun (message, rest) => (.serverHeartbeat message, rest)
  else if tag = 90 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Soup Bin Tcp Packet -/
structure ServerSoupBinTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacket

def encodeBody (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option (ServerSoupBinTcpPacket × List UInt8) := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let (serverPayload, bytes) ← ServerPayload.decode serverPacketType bytes
  pure ({ serverPayload }, bytes)

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (ServerSoupBinTcpPacket × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ServerSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end ServerSoupBinTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupBinTcpPacket : List ServerSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupBinTcpPacket.encode message.serverSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupBinTcpPacket ← decodeAll ServerSoupBinTcpPacket.decode bytes.length bytes
  pure { serverSoupBinTcpPacket }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.decode ServerSoupBinTcpPacket.decode_encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket _ (encodeMany_length_ge ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket), some_bind]
  rfl

end ServerPacket

end Omi.NasdaqNordicequitiesOrderentryOuchV50114Server
