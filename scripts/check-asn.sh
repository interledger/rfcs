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
	curl --silent -X POST \
		--data-urlencode '__EVENTTARGET=' \
		--data-urlencode '__EVENTARGUMENT=' \
		--data-urlencode '__LASTFOCUS=' \
		--data-urlencode '__VIEWSTATE=/wEPDwUKLTc1MTgyNjExOA9kFgJmD2QWAgIDD2QWAgIBD2QWCgIBDxBkDxYJAgICAwIEAgUCBgIHAggCCQIKFgkQBQ5JVFMgQ0FNIHYxLjMuMgUOSVRTIENBTSB2MS4zLjJnEAUPSVRTIERFTk0gdjEuMi4yBQ9JVFMgREVOTSB2MS4yLjJnEAUJSVRTIEoyNzM1BQlJVFMgSjI3MzVnEAULTkJBUCB2Ni4yLjAFC05CQVAgdjYuMi4wZxAFDFJBTkFQIFY2LjIuMAUMUkFOQVAgVjYuMi4wZxAFClJSQyB2OC42LjAFClJSQyB2OC42LjBnEAUMUzFBUCB2OC4xMC4wBQxTMUFQIHY4LjEwLjBnEAUIVEFQLTAzMTAFCFRBUC0wMzEwZxAFC1gyQVAgdjguOS4wBQtYMkFQIHY4LjkuMGcWAWZkAg0PEGRkFgFmZAIhDxBkZBYBZmQCIw9kFgICAQ8QZGQWAWZkAikPDxYCHgRUZXh0BVp7DQogICJuYW1lIjoiQWRhbSIsDQogICJmaXJzdC13b3JkcyI6IkhlbGxvIFdvcmxkIiwNCiAgImFnZSI6ew0KICAgICJiaWJsaWNhbCI6OTMwDQogIH0NCn1kZBgBBR5fX0NvbnRyb2xzUmVxdWlyZVBvc3RCYWNrS2V5X18WAQUdY3RsMDAkTWFpbkNvbnRlbnQkY2JOb1JlbGF4ZWS9r/9ep6vlfHBa1v0m9rFsUTVAg3p/w6Px4rcxgVnXcw==' \
		--data-urlencode '__VIEWSTATEGENERATOR=CA0B0334' \
		--data-urlencode '__EVENTVALIDATION=/wEdACTvBuL05c27tEMecJdb7IRZ1Cn+EpYSvY49XXrT29VY4DlKzLXE7UdGV+Sp4JynSVOUQai7x7H8epe7LjGkdO1cgsEkCnvatlsBmoGzDwbENG99/MJQf84nGOuvH0Nqme50SlF0/MXZPvJGTJ0aiVXFjEbYeNpryczPOfAPjZw2TmCy9br2E6vqtwSo6KnqMCHIg3IlVtr0nSnHI6hlNOXtzxTmDO+Ma32VfVY1O54Wy0hi53xAgYeVolslSp4aO/uZQKCK8xCNszfebGf8YBtrE5yR22Zoj/1cYhs6e19KIZKKpUt+2UttFP/gcQ0eOF+UdPim13mnFKHrBb176tgjv459Su9vLXbk7rGI/PHmqd2HCK7GUrcrWVpACKFv2zCj/gTCNXHIux3sexLf2Mopi4gRuE0nuD6kWraOU4UYoGvORuieq817u1hpS2zmlXhRoegCA2sek8Eg96dPkbe7PDNaWsaFKb9VSHutwb/KaCXkW74IirQHSJdIWFDq3cm2kYKX8ahKano1pLMtFiSPavO4bWHbVWZygdSrHRt9UsSuHQk/BqLrHPQunBKreLXh1857L5mvx/OFU09s5cbOyjCnzAPFMOG1G4/BC4S5xhCiOdJHJUbujzdFcUQssJa95wMqz3SaX35ivgp6JALGcpMWZ7v8HJ2Gj4qwh9D1X9Y1v2qihQEbJxac2paax0I9iDsfElO+PLcN/u2h7Km2mYq67nirnTn51aDV5CXNC1r9bT38/5lWR/G/on5UtiU+I9+9txLsDx7sc0JrUj3zVyNZYO29gB72z26Q+eQbXw==' \
		--data-urlencode 'ctl00%24MainContent%24tbASN1Code@-' \
		--data-urlencode 'ctl00%24MainContent%24CompileButton=Compile' \
		'http://asn1-playground.oss.com/' |
	grep 'MainContent_ConsoleOutput' |
	sed 's/<br\/>/\n/g' |
	# Print the parser output.
	tee /dev/stderr |
	grep --quiet '0 error messages, 0 warning messages'
