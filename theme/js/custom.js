const link = document.querySelector('.href-git-edit-button');
if (link) {
  console.log(link);
  const filename = link.getAttribute('href');
  const dotIndex = filename.lastIndexOf(".");
  let name = filename.slice(0, dotIndex);
  // const extension = filename.slice(dotIndex + 1);
  name = name.replace(/\./g, "/");
  const prefixedHref = 'https://github.com/UniMath/agda-unimath/edit/master/src/' + name + ".lagda.md";
  link.setAttribute('href', prefixedHref);
} else {
  console.error('Could not find a link with the class "href-git-edit-button"');
}