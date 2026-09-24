import miax.miaxoptions.complextopofmarket.MiaxOptions_ComplexTopOfMarket_v1_1

/-!
# Miami International Holdings Complex Top Of Market tests

Payloads captured in omi-data-packets, decoded by the generated definition: udp datagrams as they
are, tcp segments reassembled into the stream each side sent. Each must decode and leave nothing
behind, which `decide` checks at build time.
-/

namespace Omi.MiaxMiaxoptionsComplextopofmarketMachV11.Tests

/-- Miax/MiaxOptions.ComplexTopOfMarket.Mach.v1.1/Heartbeat.pcap: 12 bytes -/
def captureHeartbeat : List UInt8 :=
  [0xf7, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0c, 0x00, 0x00, 0x01]

example : (Omi.MiaxMiaxoptionsComplextopofmarketMachV11.Packet.decode captureHeartbeat).isSome = true := by
  decide +kernel

/-- Miax/MiaxOptions.ComplexTopOfMarket.Mach.v1.1/SystemStatusMessage.pcap: 30 bytes -/
def captureSystemstatusmessage : List UInt8 :=
  [0xd6, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1e, 0x00, 0x03, 0x01, 0x53, 0x07, 0x54, 0x1a, 0x36, 0x43, 0x54, 0x4f, 0x4d, 0x31, 0x2e, 0x30, 0x20, 0x01, 0x00, 0x00, 0x00, 0x31]

example : (Omi.MiaxMiaxoptionsComplextopofmarketMachV11.Packet.decode captureSystemstatusmessage).isSome = true := by
  decide +kernel

end Omi.MiaxMiaxoptionsComplextopofmarketMachV11.Tests
