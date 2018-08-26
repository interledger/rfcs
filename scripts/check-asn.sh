#!/usr/bin/env bash

if [[ $(git diff master -- asn1 | wc -l) == 0 ]]; then
	echo 'No changes were made in the asn1 folder, skipping this check'
	exit
fi

cat ./asn1/*.asn |
	# Convert POST body to CRLF
	sed $'s/$/\r/' |
	# "@-" means input is from stdin.
	# "%24" is a URL-encoded "$" (curl expects the field name already escaped).
	curl --silent --no-keepalive -X POST \
	    --header 'Expect:' \
	    --header 'User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_13_6) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/67.0.3396.99 Safari/537.36' \
		--header 'Referer: http://asn1-playground.oss.com/' \
		--data-urlencode '__EVENTTARGET=' \
		--data-urlencode '__EVENTARGUMENT=' \
		--data-urlencode '__LASTFOCUS=' \
		--data-urlencode '__VIEWSTATE=/wEPDwUJNzc4NDQyOTQ5D2QWAmYPZBYCAgMPFgIeB2VuY3R5cGUFE211bHRpcGFydC9mb3JtLWRhdGEWAgIBD2QWMAIBDxBkDxYJAgICAwIEAgUCBgIHAggCCQIKFgkQBQ5JVFMgQ0FNIHYxLjMuMgUOSVRTIENBTSB2MS4zLjJnEAUPSVRTIERFTk0gdjEuMi4yBQ9JVFMgREVOTSB2MS4yLjJnEAUJSVRTIEoyNzM1BQlJVFMgSjI3MzVnEAULTkJBUCB2Ni4yLjAFC05CQVAgdjYuMi4wZxAFDFJBTkFQIFY2LjIuMAUMUkFOQVAgVjYuMi4wZxAFClJSQyB2OC42LjAFClJSQyB2OC42LjBnEAUMUzFBUCB2OC4xMC4wBQxTMUFQIHY4LjEwLjBnEAUIVEFQLTAzMTAFCFRBUC0wMzEwZxAFC1gyQVAgdjguOS4wBQtYMkFQIHY4LjkuMGcWAWZkAgMPDxYCHgtOYXZpZ2F0ZVVybGVkZAIFDw8WAh4EVGV4dAVDQzpcd2Vic2l0ZVx4XDI5NDcwREI2LzI4YTBkMjExLTA2NzQtNDUyNy04ZjQ5LTE4ODllZmE1Mzk3YS5zcGVjLmFzbmRkAgcPDxYCHgdWaXNpYmxlaGRkAgkPDxYCHwNnZGQCCw8PFgIfA2hkZAINDxBkZBYBZmQCDw8QDxYCHgtfIURhdGFCb3VuZGdkEBUBBlJvY2tldBUBBlJvY2tldBQrAwFnZGQCEQ9kFgQCAw8PFgIfAmVkZAIFDw8WAh8CZWRkAhsPDxYCHwIFB0NvbXBpbGVkZAIfDw8WAh8CBRZDb21waWxlZCBzdWNjZXNzZnVsbHkuZGQCJQ8PFgIfAWVkZAInDw8WAh8BZWRkAikPEGRkFgFmZAIrD2QWAgIBDxAPFgIfBGdkEBUBBlJvY2tldBUBBlJvY2tldBQrAwFnFgFmZAIxDw8WAh8CBWF7DQogICJuYW1lIjoiRmFsY29uIiwNCiAgImZ1ZWwiOiJzb2xpZCIsDQogICJzcGVlZCI6eyJtcGgiOjE4MDAwfSwNCiAgInBheWxvYWQiOlsiQ2FyIiwgIkdQUyJdDQp9ZGQCNQ8PFgIfAWVkZAI3Dw8WAh8BZWRkAjkPDxYCHwFlZGQCOw8PFgIfAWVkZAI9Dw8WAh8BZWRkAj8PDxYCHwFlZGQCQQ8PFgIfAWVkZAJDDw8WAh8CBY0DPGJyLz5PU1MgQVNOLTFTdGVwIFZlcnNpb24gOC4yPGJyLz5Db3B5cmlnaHQgKEMpIDIwMTcgT1NTIE5va2FsdmEsIEluYy4gIEFsbCByaWdodHMgcmVzZXJ2ZWQuPGJyLz5UaGlzIHByb2R1Y3QgaXMgbGljZW5zZWQgZm9yIHVzZSBieSAmcXVvdDtPU1MgTm9rYWx2YSwgSW5jLiZxdW90Ozxici8+PGJyLz5DMDA0M0k6IDAgZXJyb3IgbWVzc2FnZXMsIDAgd2FybmluZyBtZXNzYWdlcyBhbmQgMCBpbmZvcm1hdG9yeSBtZXNzYWdlcyBpc3N1ZWQuPGJyLz48YnIvPjxici8+QVNOMVNURVA6IExpc3Qgb2YgdmFsaWQgdW5yZWZlcmVuY2VkIGFuZC9vciB1c2VyLWRlZmluZWQgUERVIG51bWJlcnMgYW5kIGFzc29jaWF0ZWQgUERVIG5hbWVzOjxici8+PGJyLz4gICAgICAgMSAgUm9ja2V0PGJyLz48YnIvPmRkGAEFHl9fQ29udHJvbHNSZXF1aXJlUG9zdEJhY2tLZXlfXxYCBR1jdGwwMCRNYWluQ29udGVudCRjYk5vUmVsYXhlZAUXY3RsMDAkTWFpbkNvbnRlbnQkY2JQRFVDik8yPPGAtRT7Ji3MwHCxAxN4TO0bWA4L0X5Fdyh1Lw==' \
		--data-urlencode '__VIEWSTATEGENERATOR=CA0B0334' \
		--data-urlencode '__EVENTVALIDATION=/wEdACVuz9z4TLlZe/rwylE8y76d1Cn+EpYSvY49XXrT29VY4DlKzLXE7UdGV+Sp4JynSVOUQai7x7H8epe7LjGkdO1cgsEkCnvatlsBmoGzDwbENG99/MJQf84nGOuvH0Nqme50SlF0/MXZPvJGTJ0aiVXFjEbYeNpryczPOfAPjZw2TmCy9br2E6vqtwSo6KnqMCHIg3IlVtr0nSnHI6hlNOXtzxTmDO+Ma32VfVY1O54Wy0hi53xAgYeVolslSp4aO/uZQKCK8xCNszfebGf8YBtrE5yR22Zoj/1cYhs6e19KIZKKpUt+2UttFP/gcQ0eOF+UdPim13mnFKHrBb176tgjv459Su9vLXbk7rGI/PHmqd2HCK7GUrcrWVpACKFv2zC971gRdBwfx2ssnKbT5Erbi4gRuE0nuD6kWraOU4UYoFr9bT38/5lWR/G/on5UtiVE9GHQGX3ObY5z4cuBtZee4dfOey+Zr8fzhVNPbOXGzmvORuieq817u1hpS2zmlXhRoegCA2sek8Eg96dPkbe7PDNaWsaFKb9VSHutwb/KaCXkW74IirQHSJdIWFDq3cm2kYKX8ahKano1pLMtFiSPavO4bWHbVWZygdSrHRt9UsSuHQk/BqLrHPQunBKreLXKMKfMA8Uw4bUbj8ELhLnGEKI50kclRu6PN0VxRCywlr3nAyrPdJpffmK+CnokAsZykxZnu/wcnYaPirCH0PVf1jW/aqKFARsnFpzalprHQj2IOx8SU748tw3+7aHsqbaZirrueKudOfnVoNXkJc0LpcFJ22uVVocHG0JONK06NKSzTLql4w3ApFe0TLCa4EY=' \
		--data-urlencode 'ctl00%24MainContent%24listSpecsInput=Enter manually' \
		--data-urlencode 'ctl00%24MainContent%24CompileButton=Compile' \
		--data-urlencode 'ctl00%24MainContent%24tbASN1Code@-' \
		--data-urlencode 'ctl00%24MainContent%24cbNoRelaxed=on' \
		--data-urlencode 'ctl00%24MainContent%24cbPDU=on' \
		--data-urlencode 'ctl00%24MainContent%24CompileButton=Compile' \
		'http://asn1-playground.oss.com/' |
    grep 'MainContent_ConsoleOutput' |
    sed 's/<br\/>/\n/g' |
	# Print the parser output.
	tee /dev/stderr |
    grep --quiet '0 error messages, 0 warning messages'
