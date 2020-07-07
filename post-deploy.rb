require 'octokit'

client = Octokit::Client.new(:access_token => ENV['GITHUB_TOKEN'])

repo = Octokit::Repository.from_url("https://github.com/NICTA/cogent")

tags = client.tags("NICTA/cogent")
tagnames = tags.map { |t| t.name }

auto_deploy_tags_all = tagnames.select { |t| t =~ /^auto-deploy-*/ }

# In reverse order.

auto_deploy_tags_sorted = auto_deploy_tags_all.sort{ |x,y|

  pre = "auto-deploy-"

  nx = x.delete_prefix(pre).to_i
  ny = y.delete_prefix(pre).to_i
  ny <=> nx

}

# No matter what, always keep the most recent.

auto_deploy_tags_sorted.shift

if auto_deploy_tags_sorted.nil? then

  puts "No auto-deployed releases."
  exit

elsif auto_deploy_tags_sorted.length == 0 then

  puts "Only one release available, do not delete."
  exit

end

auto_deploy_tags = auto_deploy_tags_sorted

auto_deploy_tags.each { |t|

  release = client.release_for_tag(repo, t)
  release_url = release.url

  del_rel_res = client.delete_release(release_url)
  puts "Deleting release " + t
  if del_rel_res then puts "Succeeded!" else puts "Failed!" end

  del_tag_res = client.delete_ref(repo, "tags/" + t)
  puts "Deleting tag " + t
  if del_tag_res then puts "Succeeded!" else puts "Failed!" end

}

puts "Clean-up done."
