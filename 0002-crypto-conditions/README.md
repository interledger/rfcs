# Crypto Conditions

See [here](https://interledger.org/five-bells-condition/spec.html) for the rendered spec.

## Rendering

Uses [kramdown-rfc2629](https://github.com/cabo/kramdown-rfc2629/), [xml2rfc](http://xml2rfc.ietf.org/) and [Grunt](http://gruntjs.com/) with [Grunt kramdown_rfc2629 task](https://github.com/hildjj/grunt-kramdown-rfc2629/)


From root directory of the repo run:

    npm install
    grunt kramdown-rfc2629
   
To watch edits to 0002-crypto-conditions.md and auto-generate output when changes are saved run:

    grunt watch
    

## Files

* [README.md](README.md) - this file
* [0002-crypto-conditions.md](0002-crypto-conditions.md) - canonical (mostly) markdown format file
* [output/0002-crypto-conditions.xml](output/0002-crypto-conditions.xml) - RFC in XML format
* [output/0002-crypto-conditions.txt](output/0002-crypto-conditions.txt) - RFC in text format
* [output/0002-crypto-conditions.html](output/0002-crypto-conditions.html) - RFC in html format
