'use strict'

const fs = require('fs')
const ejs = require('ejs')
const glob = require('glob')
const path = require('path')
const exec = require('child_process').execSync
const marked = require('marked')
const cheerio = require('cheerio')
const fm = require('front-matter')

// We need a custom renderer to make sure we generate the same header IDs as
// Github.
const renderer = new marked.Renderer()
renderer.heading = function (text, level, raw) {
  const candidateId = raw
    .toLowerCase()
    .replace(/[^\w\- ]+/g, '')
    .replace(/ /g, '-')

  return '<h'
    + level
    + ' id="'
    + this.options.headerPrefix
    + candidateId
    + '">'
    + text
    + '</h'
    + level
    + '>\n';
}

// Override relative links from .md files to the base folder
// (Allows github to be linked properly, and website as well)
renderer.link = function (href, title, text) {
  // Converts something like `../xxxx-<anything>/xxxx-<anything>.md` to `../xxxx-<anything>`
  href = href.replace(/^(\.{2}\/\d{4}-.*)\/(\d{4}-.*\.md)$/g, '$1')
  return marked.Renderer.prototype.link.call(this, href, title, text);
};

let cwd = path.resolve(__dirname, '..')
exec('rm -rf web', { cwd })
exec('git clone git@github.com:interledger/rfcs.git --branch gh-pages --single-branch web', { cwd })
exec('cp -r ????-* web', { cwd })
exec('cp -r shared web', { cwd })
exec('cp -r asn1 web/asn1', { cwd })

const template = ejs.compile(fs.readFileSync('tmpl/rfc.ejs.html', 'utf8'))
const files = glob.sync('????-*/????-*.md')
let buildPass = true

files.forEach((file) => {

  const fileContent = fs.readFileSync(file, 'utf8')
  const fmContent = fm(fileContent)

  if(fmContent.attributes.deprecated) {
    console.log("Skipped deprecated RFC in " + file)
    return
  }

  if(!fmContent.attributes.title) {
    buildPass = false;
    console.error("No title specified for " + file)
    return
  }
  const title = fmContent.attributes.title

  if(!fmContent.attributes.draft) {
    buildPass = false;
    console.error("Draft number required for " + file)
    return
  }
  const draftNumber = fmContent.attributes.draft

  if((draftNumber^0) !== draftNumber && draftNumber !== 'FINAL') {
    buildPass = false;
    console.error("Invalid draft number found for " + file)
    return
  }

  const renderedMarkdown = marked(fmContent.body, { renderer })
  const $ = cheerio.load(renderedMarkdown)
  
  const permalink = './draft-' + draftNumber + '.html'
  const draftFile = 'web/' + path.dirname(file) + '/draft-' + draftNumber + '.html'
  const indexFile = 'web/' + path.dirname(file) + '/index.html'

  // Ensure heading IDs are unique
  const idMap = new Map()
  const headings = $('h1,h2,h3,h4,h5,h6').each(function () {
    const tag = $(this)
    const id = tag.attr('id')
    let tags = idMap.get(id)
    if (!tags) {
      tags = []
      idMap.set(id, tags)
    }
    tags.push(tag)
  })

  for (let group of idMap) {
    if (group[1].length > 1) {
      group[1].forEach((tag, i) => {
        tag.attr('id', tag.attr('id') + '-' + (i + 1))
      })
    }
  }

  // Generate navigation
  const toc = $('h2, h3').map(function () {
    const tag = $(this)
    return {
      type: tag.get(0).tagName,
      title: tag.text(),
      anchor: tag.attr('id')
    }
  }).get()

  $('table').addClass('table').addClass('table-striped')

  $('p').first().addClass('intro')

  $('img').addClass('img-responsive')

  const content = $.html()
  const renderedHtml = template({ title, content, toc, permalink })

  //Versioning
  if (fs.existsSync(draftFile)) {
    const existingHtml = fs.readFileSync(draftFile, 'utf8')
    if (existingHtml != renderedHtml) {
      console.error('Draft number must be incremented if content is changed for ' + file)
      buildPass = false
      return
    }
    console.log('No changes in ' + file)
    return
  }

  console.log('Writing ' + draftFile)
  fs.writeFileSync(draftFile, renderedHtml)
  console.log('Writing ' + indexFile)
  fs.writeFileSync(indexFile, renderedHtml)

})

cwd = path.resolve(__dirname, '../web')
const status = exec('git status --porcelain', { cwd }).toString('utf8')
if (!status.length) {
  console.log('no changes')
} else {
  console.log(status)
}

process.exit(buildPass ? 0 : 1)