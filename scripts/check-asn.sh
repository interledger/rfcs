#!/usr/bin/env bash

if [ `git diff master -- asn1 | wc -l` == 0 ]
then
echo "No changes were made in the asn1 folder, skipping this check"
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
		--data-urlencode '__VIEWSTATE=/wEPDwUJOTIzNTU1MjUxD2QWAmYPZBYCAgMPZBYCAgEPZBYKAgEPEGQPFgkCAgIDAgQCBQIGAgcCCAIJAgoWCRAFDklUUyBDQU0gdjEuMy4yBQ5JVFMgQ0FNIHYxLjMuMmcQBQ9JVFMgREVOTSB2MS4yLjIFD0lUUyBERU5NIHYxLjIuMmcQBQlJVFMgSjI3MzUFCUlUUyBKMjczNWcQBQtOQkFQIHY2LjIuMAULTkJBUCB2Ni4yLjBnEAUMUkFOQVAgVjYuMi4wBQxSQU5BUCBWNi4yLjBnEAUKUlJDIHY4LjYuMAUKUlJDIHY4LjYuMGcQBQxTMUFQIHY4LjEwLjAFDFMxQVAgdjguMTAuMGcQBQhUQVAtMDMxMAUIVEFQLTAzMTBnEAULWDJBUCB2OC45LjAFC1gyQVAgdjguOS4wZxYBZmQCDQ8QZGQWAWZkAiEPEGRkFgFmZAIjD2QWAgIBDxBkZBYBZmQCKQ8PFgIeBFRleHQFWnsNCiAgIm5hbWUiOiJBZGFtIiwNCiAgImZpcnN0LXdvcmRzIjoiSGVsbG8gV29ybGQiLA0KICAiYWdlIjp7DQogICAgImJpYmxpY2FsIjo5MzANCiAgfQ0KfWRkGAEFHl9fQ29udHJvbHNSZXF1aXJlUG9zdEJhY2tLZXlfXxYBBR1jdGwwMCRNYWluQ29udGVudCRjYk5vUmVsYXhlZIkssErSHkM+Q9I95FYQz7JtxQKe+/7KUwMgkm90gRoO' \
		--data-urlencode '__VIEWSTATEGENERATOR=CA0B0334' \
		--data-urlencode '__EVENTVALIDATION=/wEdACNu03QryRSDPrjfaTiZypOg1Cn+EpYSvY49XXrT29VY4DlKzLXE7UdGV+Sp4JynSVOUQai7x7H8epe7LjGkdO1cgsEkCnvatlsBmoGzDwbENG99/MJQf84nGOuvH0Nqme50SlF0/MXZPvJGTJ0aiVXFjEbYeNpryczPOfAPjZw2TmCy9br2E6vqtwSo6KnqMCHIg3IlVtr0nSnHI6hlNOXtzxTmDO+Ma32VfVY1O54Wy0hi53xAgYeVolslSp4aO/uZQKCK8xCNszfebGf8YBtrE5yR22Zoj/1cYhs6e19KIZKKpUt+2UttFP/gcQ0eOF+UdPim13mnFKHrBb176tgjv459Su9vLXbk7rGI/PHmqd2HCK7GUrcrWVpACKFv2zCj/gTCNXHIux3sexLf2Mopi4gRuE0nuD6kWraOU4UYoGvORuieq817u1hpS2zmlXhRoegCA2sek8Eg96dPkbe7PDNaWsaFKb9VSHutwb/KaCXkW74IirQHSJdIWFDq3cm2kYKX8ahKano1pLMtFiSPxK4dCT8Gousc9C6cEqt4teHXznsvma/H84VTT2zlxs7KMKfMA8Uw4bUbj8ELhLnGEKI50kclRu6PN0VxRCywlr3nAyrPdJpffmK+CnokAsZykxZnu/wcnYaPirCH0PVf1jW/aqKFARsnFpzalprHQj2IOx8SU748tw3+7aHsqbaZirrueKudOfnVoNXkJc0LWv1tPfz/mVZH8b+iflS2JW2qCjX/fw53JtwzCwHjR6YfDQnqCSqClXwQKwZNKZ8j' \
		--data-urlencode 'ctl00%24MainContent%24tbASN1Code@-' \
		--data-urlencode 'ctl00%24MainContent%24CompileButton=Compile' \
		'http://asn1-playground.oss.com/' |
	grep 'MainContent_ConsoleOutput' |
	sed 's/<br\/>/\n/g' |
	# Print the parser output.
	tee /dev/stderr |
	grep --quiet '0 error messages, 0 warning messages'
