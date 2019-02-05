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
  href = href.replace(/^(\.{2}\/\d{4}-.*)\/(\d{4}-.*\.md)(\#[\w-]*)?$/g, '$1$3')
  return marked.Renderer.prototype.link.call(this, href, title, text);
};

let cwd = path.resolve(__dirname, '..')
const commitMessage = exec('git log -1 --pretty=%B', { cwd }).toString('utf8')
exec('rm -rf web', { cwd })
exec('git clone git@github.com:interledger/rfcs.git --branch gh-pages --single-branch web', { cwd })
exec('cp -r ????-* web', { cwd })
exec('cp -r shared web', { cwd })

const template = ejs.compile(fs.readFileSync('tmpl/rfc.ejs.html', 'utf8'))
const files = glob.sync('????-*/????-*.md')
if(commitMessage.includes("Skip Version Check")) {
  console.log('Skipping version checks. Will overwrite index.html for all specs.')
}
let buildPass = true

files.forEach((file) => {

  const rfcNumber = file.match(/^(\d\d\d\d)/)[0]
  const fileContent = fs.readFileSync(file, 'utf8')
  const fmContent = fm(fileContent)

  if(!fmContent.attributes.title && !fmContent.attributes.deprecated) {
    buildPass = false;
    console.error("No title specified for " + file)
    return
  }
  const title = fmContent.attributes.title

  if(!fmContent.attributes.draft) {
    if(fmContent.attributes.deprecated) {
      fmContent.attributes.draft = 'FINAL'
    } else {
      buildPass = false;
      console.error("Draft number required for " + file)
      return
    }
  }
  const draftNumber = fmContent.attributes.draft

  if((draftNumber^0) !== draftNumber && draftNumber !== 'FINAL') {
    buildPass = false;
    console.error("Invalid draft number found for " + file)
    return
  }

  const deprecated = fmContent.attributes.deprecated

  if(deprecated && draftNumber !== 'FINAL') {
    console.error("Deprecated RFC must be FINAL in " + file)
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
      anchor: '#' + tag.attr('id')
    }
  }).get()

  $('table').addClass('table').addClass('table-striped')

  $('p').first().addClass('intro')

  $('img').addClass('img-responsive')

  const content = $.html()
  const renderedHtml = template({ title, content, toc, rfcNumber, draftNumber, deprecated })

  //Versioning
  if(!commitMessage.includes("Skip Version Check")) {
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
  }

  console.log('Writing ' + draftFile)
  fs.writeFileSync(draftFile, renderedHtml)
  console.log('Writing ' + indexFile)
  fs.writeFileSync(indexFile, renderedHtml)

})

const asnFiles = glob.sync('asn1/*')
const asnToc = []
asnFiles.forEach((file) => {
  if (file.endsWith('.md')) {
    asnToc.unshift({ type: 'h2', title: 'ASN Modules', anchor: 'index.html' })
  } else {
    const asnName = path.basename(file)
    asnToc.push({ type: 'h3', title: asnName, anchor: asnName + '.html' })
  }
})
asnFiles.forEach((file) => {
  const fileContent = fs.readFileSync(file, 'utf8')
  if (file.endsWith('.md')) {
    const htmlFile = 'web/asn1/index.html'
    const content = marked(fileContent)
    const renderedHtml = template({ title: 'Interledger ASN.1', content, toc: asnToc, deprecated : false })
    console.log('Writing ' + htmlFile)
    fs.writeFileSync(htmlFile, renderedHtml)
  } else {
    const basename = path.basename(file)
    const content = '<pre><code class="nohighlight">' + escape(fileContent) + '</code></pre>'
    const renderedHtml = template({ title: basename, content, toc: asnToc, deprecated: false })
    const htmlFile = 'web/asn1/' + basename + '.html'
    console.log('Writing ' + htmlFile)
    fs.writeFileSync(htmlFile, renderedHtml)
  }
})

function escape(html) {
  return html
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;')
}

cwd = path.resolve(__dirname, '../web')
const status = exec('git status --porcelain', { cwd }).toString('utf8')
if (!status.length) {
  console.log('no changes')
} else {
  console.log(status)
}

process.exit(buildPass ? 0 : 1)
