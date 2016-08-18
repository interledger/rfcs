# Interledger Address Mapping

The Interldger Protocol defines a universal addressing scheme for any digital asset account. In order to transfer assets into existing accounts it is necessary to address these accounts.

To bootsrap this network this document proposes ILP addressing schemes for a number of existing payment networks so that connectors offering delivery into those networks can provide consistent routing information.

> _**Note:**_ This list is intended to seed a discussion. Please submit PRs with additions or changes.

# Mappings

The mappings below are proposed as ILP addresses for existing digital asset accounts:

| Network | Address Format | Example | Notes |
|---------|----------------|---------|-------|
| Bitcoin | bitcoin.<address> | bitcoin.145b3dEskk1a7Uw4gWBdpa8NFEwbfz2MgT | |
| Global Banks | iban.<iban> | iban.IE64BOFI90583812345678 | |
| Global Banks | bic.<bic>.<account_identifier> bic.BOFIIE2D.12345678 | |
| Any card network | pan.<card_pan> | pan.5432376523489763 | |
| Paypal | paypal.email.<email_address> | paypal.email.sombeody@example.com | `@` is not currently supported in ILP addresses |
| Paypal | paypal.phone.<int_phone_number> | paypal.phone.19995550123 | The `+` prefix is dropped from the number |
