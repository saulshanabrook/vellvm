(defun remove-comments (f)
  (save-excursion
    (find-file f)
    (comment-kill 100000)
    (write-file f)))

(defun coq-comment-killer (dir)
  (interactive "DDirectory for files:")
  (let ((files (directory-files-recursively dir ".*\\.v$" nil)))
    (mapcar (lambda (f) (remove-comments f)) files)))
